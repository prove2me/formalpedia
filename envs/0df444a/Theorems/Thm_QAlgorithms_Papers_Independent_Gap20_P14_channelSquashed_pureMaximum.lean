-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P14_channelSquashed_pureMaximum
-- name    : QAlgorithms.Papers.Independent.Gap20.P14.channelSquashed_pureMaximum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:31:31.087714+00:00
-- url     : https://prove2.me/theorems/e3f8e8c7-a200-488e-b2dd-ef76ad88fd8b
-- title:
--   Pure-input reduction and attainment of the finite channel optimization
-- statement:
--   Let $\mathcal N:A'\to B$ be a CPTP map between positive finite-dimensional systems, and let $A$ be a reference copy of $A'$. For any normalized input density operator $\rho_{AA'}$, apply the identity to $A$ and $\mathcal N$ to $A'$. Define $E_{\rm sq}(\mathcal N)$ by optimizing the output squashed entanglement over these density operators. There exists a normalized pure input $\lvert\phi\rangle_{AA'}$ attaining this optimization, so that
--
--   $$
--   E_{\rm sq}(\mathcal N)=\max_{\rho_{AA'}} E_{\rm sq}(A;B)_{({\rm id}\otimes\mathcal N)(\rho)}=E_{\rm sq}(A;B)_{({\rm id}\otimes\mathcal N)(\lvert\phi\rangle\langle\phi\rvert)}.
--   $$
--
--   Thus the finite-input maximum can be taken over pure inputs. The claim concerns the computed optimization, not an arbitrary parameter representing capacity.
-- source:
--   Fundamental rate-loss tradeoff for optical quantum key distribution, arXiv:1504.06390v1, PDF p. 3, Eq. (3): pure-input reduction and finite-input maximum

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P14

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1504.06390v1, PDF p.3, Eq.(3) and its adjacent discussion:
the finite-dimensional mixed-input optimization is attained by a normalized
pure bipartite input with a reference copy of the input space.
The IsGreatest clause retains attainment, not merely a supremum identity. -/
theorem channelSquashed_pureMaximum
    {I O : Type} [Fintype I] [Fintype O] [Nonempty I] [Nonempty O]
    (N : Superop I O) (hN : IsChannel N) :
    ∃ psi : EuclideanSpace ℂ (I × I), ‖psi‖ = 1 ∧
      IsGreatest (channelSquashedValues N)
        (squashedEntanglement (idTensorSuperop N (pureDensity psi))) ∧
      channelSquashedEntanglement N =
        squashedEntanglement (idTensorSuperop N (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P14

end
