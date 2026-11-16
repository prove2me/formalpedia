-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_Supplement_exact_dimension
-- name    : StabPauli1264.Grouped.Supplement.exact_dimension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:49:22.140192+00:00
-- url     : https://prove2.me/theorems/7adab613-d619-41a3-9dfb-976f48fd5921
-- title:
--   Theorem 2.1 — Exact dimension
-- statement:
--   Let $M=(P_1,\ldots,P_m)$ be any window and $F_M\subseteq\{-1,0,1\}^m$ its class of pure stabilizer responses. A set $T\subseteq[m]$ is pseudo-shattered by $F_M$ if and only if the Paulis $P_i$, $i\in T$, pairwise commute and have linearly independent labels. Consequently, for every $0<\gamma\le1$,
--
--   $$d_\pm(F_M)=d_P(F_M)=d_{\mathrm{VC}}(A_M)=d_{\mathrm{fat}}(F_M,\gamma)=r(M).$$
--
--   Here $d_P$ uses strict threshold events, $d_\pm$ exact sign shattering, $d_{\mathrm{fat}}$ the weak margin $u_i(f(i)-t_i)\ge\gamma$, and $d_{\mathrm{VC}}(A_M)$ is the VC dimension of the agreement class on $[m]\times\{\pm1\}$. The identity determines the uniform-convergence rate of single-Pauli learning by the commuting rank.
--
--   Differences from the source:
--   - encoding: index set [m] and sign set {±1} of the agreement domain → Fin m and Bool (true = +1); reason: relabelling only
--   - encoding: responses f_σ(i) = tr(σP_i) → real part of tr(σ_T P_i) for the projector σ_T of a valid tableau T; reason: the trace is real for Hermitian operators; every pure stabilizer state has a valid tableau
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Theorem 2.1 and Eq. (5), p. 6; conventions pp. 5, 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Supplement_Structure
set_option autoImplicit false

namespace StabPauli1264.Grouped.Supplement

open QAlgorithms.Stabilizer StabPauli1264.Grouped
open scoped BigOperators Classical

/-- Theorem 2.1 (Exact dimension), p. 6: pseudo-shattered sets are exactly the commuting sets with
independent labels, and all four dimensions equal the commuting rank, for every `0 < γ ≤ 1`. -/
theorem exact_dimension {n m : ℕ} (M : Window n m) :
    (∀ T : Finset (Fin m), PseudoShatters (responses M) T ↔ IsContext M T ∧ IndepLabels M T) ∧
    signDim (responses M) = commutingRank M ∧
    pseudoDim (responses M) = commutingRank M ∧
    agreementVCDim (responses M) = commutingRank M ∧
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → fatDim (responses M) γ = commutingRank M := by sorry

end StabPauli1264.Grouped.Supplement
