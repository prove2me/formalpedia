-- Prove2me | Theorems.Thm_ThreshRankBIS_eq_16
-- name    : ThreshRankBIS.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:13:46.587203+00:00
-- url     : https://prove2.me/theorems/e92c9cef-6df5-42a2-9dd4-936598c47c12
-- title:
--   Display (16) — $m_\lambda(w,t)\le Ke^{v_d}q^{-\theta t/2}\le K\exp\{v_d-ct\}$, $v_d=3ne^{-ad}$
-- statement:
--   Fix $0<\rho<1$ and $\lambda_0>0$. There are constants $a,c>0$, and the constant $0<\theta\le1/16$ of Lemma 11, depending only on $\rho,\lambda_0$, such that for every simple $d$-regular bipartite graph with $|X|=|Y|=n$ and $d\ge1$, every list $\mathcal C$ of approximate cuts satisfying (7) with $K=|\mathcal C|$, every fugacity $\lambda\ge\lambda_0$, every neighborhood size $w$ and every deficit $t\ge1$,
--
--   $$
--   m_\lambda(w,t)\le K\,e^{v_d}q^{-\theta t/2}\le K\exp\{v_d-ct\},\qquad v_d=3ne^{-ad}. \tag{16}
--   $$
--
--   Display (16) is the container bound of the paper: the weight of the high-deficit classes decays exponentially in the deficit, with a prefactor $Ke^{v_d}$ that is $2^{O(k)}\mathrm{poly}(n)$ once $d\ge C\log(n+1)$.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - reading: here θ is from Lemma 11 → ∃ θ with 0 < θ ≤ 1/16, chosen with a and c before the graph; reason: Lemma 11 only asserts the existence of such a θ (any sufficiently small θ works), and a Lean statement cannot name the witness of another statement
--   - generalization: the fugacity λ, rational where it is an algorithm input (p.3) → λ a real number with the same lower bound; reason: the statement is about the combinatorial weights only and holds for every real λ in the range; it specializes to rational λ
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), display (16), p.15; standing list hypothesis §4, p.12

import Mathlib
import Definitions.Def_ThreshRankBIS_SatisfiesEq7
import Definitions.Def_ThreshRankBIS_mWeight
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Display (16)**, p.15. Fix `0 < ρ < 1` and `λ_0 > 0`. There are constants `a, c > 0` (and
the constant `0 < θ ≤ 1/16` of Lemma 11), depending only on `ρ, λ_0`, such that for every
`d`-regular bipartite `G` with `d ≥ 1`, every list `𝒞` of approximate cuts satisfying (7)
(`K = |𝒞|`), every fugacity `λ ≥ λ_0`, every neighborhood size `w` and every deficit `t ≥ 1`,
`m_λ(w, t) ≤ K e^{v_d} q^{−θt/2} ≤ K exp{v_d − ct}`, `v_d = 3ne^{−ad}`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), p.15, display (16);
standing list hypothesis §4, p.12.

**Formalization Note.** `θ` is existentially quantified with the range Lemma 11 gives it; Lean
cannot name the witness of another statement. `λ` is real. -/
theorem eq_16 (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (lam0 : ℝ) (hlam0 : 0 < lam0) :
    ∃ a c θ : ℝ, 0 < a ∧ 0 < c ∧ 0 < θ ∧ θ ≤ 1 / 16 ∧
      ∀ {n d : ℕ} (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
      ∀ 𝒞 : Finset (Finset (V n)), SatisfiesEq7 ρ E 𝒞 →
      ∀ lam : ℝ, lam0 ≤ lam → ∀ w t : ℕ, 1 ≤ t →
        mWeight E lam w t ≤
            (#𝒞 : ℝ) * Real.exp (3 * n * Real.exp (-(a * d))) * (1 + lam) ^ (-(θ * t / 2)) ∧
          (#𝒞 : ℝ) * Real.exp (3 * n * Real.exp (-(a * d))) * (1 + lam) ^ (-(θ * t / 2)) ≤
            (#𝒞 : ℝ) * Real.exp (3 * n * Real.exp (-(a * d)) - c * t) := by sorry

end ThreshRankBIS
