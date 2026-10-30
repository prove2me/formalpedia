-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_equation12
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.equation12
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:42:14.340988+00:00
-- url     : https://prove2.me/theorems/57726ed3-98d7-4bb0-b15d-e6fa35f1d6f6
-- title:
--   equation-12
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   Let $\mathcal N:AB\to CD$ be a CPTP bipartite channel. Suppose it has a CPTP extension $\mathcal M:AB_1B_2\to CD_1D_2$ satisfying simultaneous Bob input/output swap covariance and $\operatorname{Tr}_{D_2}\circ\mathcal M=\mathcal N\otimes\operatorname{Tr}_{B_2}$. Then
--   $$
--   \operatorname{Tr}_D\circ\mathcal N=\operatorname{Tr}_D\circ\mathcal N\circ\mathcal R_B^\pi,
--   \qquad \mathcal R_B^\pi(X)=\operatorname{Tr}(X)\frac{I_B}{\dim B}.
--   $$
--   Equivalently its Choi matrix satisfies $\operatorname{Tr}_D\Gamma(\mathcal N)=\operatorname{Tr}_{BD}\Gamma(\mathcal N)\otimes I_B/\dim B$ with canonical register permutation. Thus two-extendibility already implies Bob-to-Alice non-signaling, without a PPT assumption.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 4, equation-12

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF pp.4–5, (12),(18), Appendix A p.22: every two-extendible channel
is Bob-to-Alice non-signaling. No PPT assumption is needed. -/
theorem equation12 [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (N : Superop (A × B) (C × D)) (hN : IsChannel N)
    (hext : HasExtension false false (choi N)) : BobToAliceNS (choi N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
