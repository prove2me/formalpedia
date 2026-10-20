-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_uniformCollisionGain
-- name    : QAlgorithms.Papers.Independent.Information100.P76.uniformCollisionGain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:57:40.694452+00:00
-- url     : https://prove2.me/theorems/ce0dc980-2182-4abf-a94b-46e403cec5ef
-- title:
--   Theorem 3.1: uniform collision gain
-- statement:
--   Let $\Phi:M_q(\mathbb C)\to M_q(\mathbb C)$ be CPTP, with $q\ge1$. For a finite collision $C=(U,\tau)$, write $\Phi_C$ for its system channel, $\Gamma_C$ for its active bath channel, and $g_C=\max_\rho S(\Gamma_C(\rho))-S(\tau)$, where the maximum ranges over normalized input density matrices. All entropies are in bits. Let $\kappa(\Phi)$ be the independent-reference extension cost of Definition 1.3: the positive-error limit is taken at each fixed positive-definite input before the supremum over such inputs. With $D_\diamond$ denoting half diamond distance,
--
--   $$\kappa(\Phi)=\lim_{\eta\downarrow0}\inf_{C:\,D_\diamond(\Phi_C,\Phi)\le\eta}g_C.$$
--
--   The infimum ranges over every positive finite bath dimension and every actual initializer; no optimizing collision or dimension bound is assumed. This identifies the intrinsic variational cost with uniform physical collision gain.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 6, Theorem 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF p.6, Theorem 3.1: uniform collision gain, with the limit outside optimization. -/
theorem uniformCollisionGain {q : ℕ} (hq : 0 < q)
    (Phi : Superop (Fin q) (Fin q)) (hPhi : IsChannel Phi) :
    Tendsto (approximateCollisionCost Phi) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (intrinsicCost Phi)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
