-- Prove2me | Theorems.Thm_SAInterp_Res2_lemma_7_6
-- name    : SAInterp.Res2.lemma_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:41:49.951197+00:00
-- url     : https://prove2.me/theorems/8f2294be-d804-4bb2-b537-7efbff14adf5
-- title:
--   Lemma 7.6 — Q_{|A|}(k) is the joint moment E_{D_k}[∏_{i∈A} X_i | π]
-- statement:
--   Let $\pi=(\pi_i)_{i\in[n-1]}$ be any layer permutations of $\mathrm{CPLS}_n$, let $k\in[n]$, and let $A\subseteq[n]\setminus\{1\}$ with $|A|\le n$. With $X_i=1$ iff path $i$ is coloured ($i\notin S$),
--   $$Q_{|A|}(k)=\mathop{E}_{D_k}\Bigl[\prod_{i\in A}X_i\ \Big|\ \pi\Bigr],\qquad Q_a(z)=\frac{(n-z)_a}{(n-1)_a}.$$
--   The moments of the colouring indicators are therefore polynomials in $k$ of degree $|A|$, which is what interpolation needs.
--
--   Differences from the source:
--   - generalization: the standing assumption of §6 "Let n be sufficiently large" → every n ≥ 1 (n ≥ k ≥ 1); reason: the lemma's statement and proof are exact for every n, and the Lean statement specializes to every large n.
--   - encoding: paths and colours 0-based (A ⊆ Fin n with 0 ∉ A for [n] ∖ {1}); E_{D_k}[· | π] as the uniform average over (S, γ, e); reason: Lean convention, same quantities.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 34 (PDF p. 36), Lemma 7.6

import Mathlib
import Definitions.Def_SAInterp_Res2_CPLSDist

namespace SAInterp.Res2

/-- Lemma 7.6 (p. 34): for any layer permutations `π` of `CPLS_n`, any `k ∈ [n]` and any
`A ⊆ [n] ∖ {1}` with `|A| ≤ n`, `Q_{|A|}(k) = E_{D_k}[∏_{i ∈ A} X_i | π]`, where `X_i = 1`
iff `i ∉ S` (0-based: path `0` is the distinguished path). -/
theorem lemma_7_6 (n : ℕ) (π : LayerPerms n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (A : Finset (Fin n)) (hA : ∀ i ∈ A, i.val ≠ 0) (hAn : A.card ≤ n) :
    (Qpoly n A.card).eval (k : ℝ) = EDkCond n k (fun S _ _ => ∏ i ∈ A, Xind S i) := by sorry

end SAInterp.Res2
