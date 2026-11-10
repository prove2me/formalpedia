-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_2_6
-- name    : SuperlatSVP.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:51.948632+00:00
-- url     : https://prove2.me/theorems/7132d7c1-0953-4f15-a007-933d76d54e05
-- title:
--   Lemma 2.6 — averaging over pairs, (2.18) and (2.19)
-- statement:
--   Let $\Gamma\subseteq L$ be full-rank lattices, $d=\det L$ and $q=[L:\Gamma]=\det\Gamma/\det L$. Let $u$ be uniform modulo $L$. For every nonnegative measurable $F:\mathbb R^n\times\mathbb R^n\to[0,\infty]$ and every fixed $c$:
--
--   1. (2.18)
--   $$\mathbb E_u\sum_{\substack{x\in L+u,\ y\in L+u-c\\ x-y\in\Gamma+c}}F(x,y)=\frac1d\sum_{z\in\Gamma+c}\int_{\mathbb R^n}F(x,x-z)\,dx ;$$
--   2. if $c$ modulo $\Gamma$ is independently uniform, then $u$ and $u-c$ modulo $L$ are independent and uniform;
--   3. (2.19) in that case,
--   $$\mathbb E_{c,u}\sum_{\substack{x\in L+u,\ y\in L+u-c\\ x-y\in\Gamma+c}}F(x,y)=\frac1{q\,d^2}\int_{\mathbb R^n}\!\int_{\mathbb R^n}F(x,y)\,dx\,dy .$$
--
--   This identity turns sums over pairs of shifted lattice points into volumes. It is the averaging step behind the moment bounds of the list-merging algorithm.
--
--   **Formalization Note** The means over $u$ and $c$ use bases $B_L$ and $B_\Gamma$, with $c$ independent of $u$ (iterated means). Statement 2 is expressed through its defining property: for every measurable $G$ that is $L$-periodic in each argument, $\mathbb E_{c,u}G(u,u-c)=\mathbb E_u\mathbb E_{u'}G(u,u')$.
--
--   Differences from the source:
--   - generalization: F : ℝⁿ × ℝⁿ → ℝ≥0 → F with values in [0,∞]; reason: every ℝ≥0-valued measurable F is an instance
--   - encoding: "u and u − c modulo L are independent and uniform" → for every measurable G, L-periodic in each argument, E_{c,u} G(u, u − c) = E_u E_{u′} G(u, u′); reason: this is the defining property of independence and uniformity of the pair of classes modulo L
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.2, p.18 (PDF p.18), Lemma 2.6, eqs. (2.18)–(2.19)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_unifMean

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 2.6 (Averaging over pairs). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.2, p.18 (PDF p.18): "Let Γ ⊆ L be full-rank lattices,
d = det L, and q = [L : Γ]. Let u mod L be uniform. For every nonnegative measurable
F : ℝⁿ × ℝⁿ → ℝ≥0 and fixed c,
E_u Σ_{x∈L+u, y∈L+u−c, x−y∈Γ+c} F(x, y) = (1/d) Σ_{z∈Γ+c} ∫_{ℝⁿ} F(x, x − z) dx. (2.18)
If c mod Γ is independently uniform, then u and u − c modulo L are independent and uniform, and
E_{c,u} Σ_{x∈L+u, y∈L+u−c, x−y∈Γ+c} F(x, y) = (1/(qd²)) ∫_{ℝⁿ}∫_{ℝⁿ} F(x, y) dx dy. (2.19)"

The conclusion has three parts: (2.18) for every `c`; the independence-and-uniformity sentence; and
(2.19).

**Formalization Note.** `L = B_Lℤⁿ`, `Γ = B_Γℤⁿ`, `d = |det B_L|`, `q = |det B_Γ|/|det B_L|`. `E_u`
is `unifMean B_L` and `E_c` is `unifMean B_Γ`, with `c` independent of `u` (iterated means). The
independence sentence is stated through its defining property: for every measurable `G` that is
`L`-periodic in each argument, `E_{c,u} G(u, u − c) = E_u E_{u'} G(u, u')`. Sums and integrals are
in `ℝ≥0∞`; `F` takes values in `ℝ≥0∞` (a generalization of `ℝ≥0`-valued `F`). -/
theorem lemma_2_6 (n : ℕ) (BL BΓ : Matrix (Fin n) (Fin n) ℝ) (hBL : BL.det ≠ 0)
    (hBΓ : BΓ.det ≠ 0) (hΓL : lat BΓ ≤ lat BL) (F : E n × E n → ℝ≥0∞) (hF : Measurable F) :
    (∀ c : E n,
      unifMean BL (fun u => ∑' xy : {xy : E n × E n // xy.1 - u ∈ lat BL ∧
          xy.2 - (u - c) ∈ lat BL ∧ xy.1 - xy.2 - c ∈ lat BΓ}, F xy) =
        (ENNReal.ofReal |BL.det|)⁻¹ *
          ∑' z : {z : E n // z - c ∈ lat BΓ}, ∫⁻ x, F (x, x - (z : E n))) ∧
    (∀ G : E n × E n → ℝ≥0∞, Measurable G →
      (∀ x y v : E n, v ∈ lat BL → G (x + v, y) = G (x, y) ∧ G (x, y + v) = G (x, y)) →
        unifMean BΓ (fun c => unifMean BL (fun u => G (u, u - c))) =
          unifMean BL (fun u => unifMean BL (fun u' => G (u, u')))) ∧
    unifMean BΓ (fun c => unifMean BL (fun u => ∑' xy : {xy : E n × E n // xy.1 - u ∈ lat BL ∧
        xy.2 - (u - c) ∈ lat BL ∧ xy.1 - xy.2 - c ∈ lat BΓ}, F xy)) =
      (ENNReal.ofReal (|BΓ.det| / |BL.det|) * ENNReal.ofReal |BL.det| ^ 2)⁻¹ *
        ∫⁻ x, ∫⁻ y, F (x, y) := by sorry

end SuperlatSVP
