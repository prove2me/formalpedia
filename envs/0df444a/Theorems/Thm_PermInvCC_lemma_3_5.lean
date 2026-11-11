-- Prove2me | Theorems.Thm_PermInvCC_lemma_3_5
-- name    : PermInvCC.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:53.284324+00:00
-- url     : https://prove2.me/theorems/d0393e45-ae09-4188-b778-c05c70c3d249
-- title:
--   Lemma 3.5 — error of sampled counts $\mathbb E\,H(J^E_T,\hat J^E)^2\le|E|(1-p)/(pk)\le q^2(1-p)/(pk)$
-- statement:
--   Fix an input pair $(x,y)\in[q]^n\times[q]^n$ with joint type $T$, an event $E\in\mathcal E$ and a sampling probability $p\in(0,1]$. Let $k:=T(E)=\sum_{e\in E}T_e$ and suppose $k>0$. Retain each coordinate independently with probability $p$, let $A$ be the random set of retained coordinates, and for $e\in E$ let
--   $$Z_e:=|\{i\in A:(x_i,y_i)=e\}|,\qquad \hat T_e:=Z_e/p,\qquad \hat J^E:=J_{(\hat T_e)_{e\in E}}.$$
--   Then
--   $$\mathbb E\,H\bigl(J^E_T,\hat J^E\bigr)^2\le\frac{|E|(1-p)}{pk}\le\frac{q^2(1-p)}{pk},$$
--   the expectation being over the coordinate sampling.
--
--   The bound converts sample size into Hellinger accuracy in Theorem 3.1.
--
--   Differences from the source:
--   - encoding: expectation over the random retained set A → finite sum over A ⊆ [n] weighted by p^|A| (1 − p)^(n − |A|); reason: this is the law of independent retention; 0⁰ = 1 covers p = 1
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 3.5, p.12

import Mathlib
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_cutEvents
import Definitions.Def_PermInvCC_hE
import Definitions.Def_PermInvCC_hell
import Definitions.Def_PermInvCC_J

namespace PermInvCC

/-- **Lemma 3.5 (Error of Sampled Counts)** (Y. Huang and Z. Ye, arXiv:2609.40116, held version
sha256 fe1797dd…, p.12). Fix an input pair `(x, y)` with joint type `T`, an event `E ∈ 𝓔` and a
sampling probability `p ∈ (0, 1]`. Let `k := T(E) > 0`. Retain each coordinate independently with
probability `p`, let `A` be the random set of retained coordinates, `Z_e := |{i ∈ A : (x_i, y_i) =
e}|` for `e ∈ E`, `T̂_e := Z_e/p` and `Ĵ^E := J_{(T̂_e)_{e∈E}}`. Then
`E H(J^E_T, Ĵ^E)² ≤ |E|(1 − p)/(pk) ≤ q²(1 − p)/(pk)`.

**Formalization Note.** The expectation over the random set `A` is the finite sum over all
`A ⊆ [n]` weighted by `p^{|A|}(1 − p)^{n−|A|}` (independent retention; `0⁰ = 1` covers `p = 1`).
`q, n ≥ 2` are the standing assumptions (p.9). -/
theorem lemma_3_5 (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) (x y : Fin n → Fin q)
    (E : Finset (Fin q × Fin q)) (hE : E ∈ cutEvents q) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hk : 0 < cellSum E (jointType x y)) :
    let k : ℝ := cellSum E (jointType x y)
    let Z : Finset (Fin n) → E → ℕ := fun A e => (A.filter fun i => (x i, y i) = e.1).card
    (∑ A : Finset (Fin n), p ^ A.card * (1 - p) ^ (n - A.card) *
        hell (JE E (jointType x y))
          (J (fun e => (Z A e : ℝ) / p) (fun _ => div_nonneg (Nat.cast_nonneg _) hp0.le)) ^ 2) ≤
      (E.card : ℝ) * (1 - p) / (p * k) ∧
    (E.card : ℝ) * (1 - p) / (p * k) ≤ (q : ℝ) ^ 2 * (1 - p) / (p * k) := by sorry

end PermInvCC
