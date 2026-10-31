-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_separable_stein
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.separable_stein
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:14:40.916001+00:00
-- url     : https://prove2.me/theorems/382e4c58-42f4-41c3-9e55-813417cddc88
-- title:
--   §II, unnumbered: separable-alternative specialization of Theorem I
-- statement:
--   Let there be finitely many, at least one, parties with nonzero finite-dimensional local spaces $H_j$, and let $\rho\in\mathcal D(H_1\otimes\cdots\otimes H_k)$. At blocklength $n\ge1$, let $S_n$ consist of all finite convex combinations of products of normalized states on the grouped local blocks $H_j^{\otimes n}$. Local states may correlate a party's copies. Write $E_R^\infty(\rho)=\inf_{n\ge1}\inf_{\omega\in S_n}D_2(\rho^{\otimes n}\Vert\omega)/n$, with base-two relative entropy and the support convention $D_2=+\infty$ when support inclusion fails.
--
--   For a two-outcome effect $0\le A_n\le I$, set $\alpha_n=\operatorname{Tr}[(I-A_n)\rho^{\otimes n}]$ and $b_n(\omega)=-\log_2\operatorname{Tr}(A_n\omega)/n$, with $-\log_2 0=+\infty$.
--
--   For every $\eta>0$ there is one effect sequence, chosen before the alternatives, such that
--   $$
--   \alpha_n\longrightarrow0,\qquad b_n(\omega_n)+\eta\ge E_R^\infty(\rho)\quad(\forall n\ge1,\ \forall\omega_n\in S_n).
--   $$
--   Conversely, for every $\eta>0$ and every effect sequence satisfying
--   $$
--   b_n(\omega_n)-\eta\ge E_R^\infty(\rho)\quad(\forall n\ge1,\ \forall\omega_n\in S_n),
--   $$
--   one has $\alpha_n\longrightarrow1$.
--
--   This is the fully multipartite separable-alternative interface for gap:f18e3b0cef281528612df02b. No entanglement assumption on the null state is needed.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 6, §II, unnumbered: separable-alternative specialization of Theorem I

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6 Eq.(15) and p.5 Theorem I: both clauses for fully separable
alternatives, with the same E_R^infinity and the same effects for all alternatives. -/
theorem separable_stein {P : Type} [Fintype P] [DecidableEq P] [Nonempty P]
    (d : P → ℕ) (hd : ∀ j, 0 < d j)
    (rho : Mat (PartyReg d)) (hrho : IsDensityMatrix rho) :
    SteinClauses (separableFamily d) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
