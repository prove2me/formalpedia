-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_gateTeleportation_transposes
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.gateTeleportation_transposes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:48:12.757004+00:00
-- url     : https://prove2.me/theorems/6dae9006-a842-4c0e-92a4-7c445c41aa12
-- title:
--   Figure 9: rectangular gate teleportation transposes channels
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   There is a single fixed physical one-slot parallel circuit $A$ such that, for every CPTP map $\Lambda:\mathcal L(\mathbb C^d)\to\mathcal L(\mathbb C^D)$ and every operator $Y$,
--
--   $$A_{\rm succ}(\Lambda)(Y)=\mathcal T_\Lambda(Y)=\frac{1}{Dd}\Lambda^T(Y).$$
--
--   Here $\mathcal T_\Lambda$ is the contraction of the normalized $d$-dimensional maximally entangled resource with the successful $D$-dimensional Bell outcome, and $\Lambda^T$ is Kraus transposition in computational coordinates. On a density matrix $\rho$, the physical outcome probability is $\operatorname{Tr}(\Lambda^T(\rho))/(Dd)$. A CPTP channel can have a trace-changing transpose. This provides the rectangular channel version of gate teleportation.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 23, §4.2 Figure 9: generalized gate teleportation transposes a channel

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P07

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P06 (Choi)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

/-- arXiv:2110.00258v5 PDF pp.22--23, Figure 9: one fixed circuit transposes
every rectangular CPTP input channel. The heralding probability on a state is
Tr(Lambda^T(rho))/(Dd), rather than necessarily 1/(Dd). -/
theorem gateTeleportation_transposes (d D : ℕ) (hd : 0 < d) (hD : d ≤ D) :
    ∃ A : Parallel d D D d 1,
      ∀ Lambda : Superop (Fin d) (Fin D), IsChannel Lambda → ∀ X,
        A.run (piSuperop (fun _ : Fin 1 => Lambda)) X = gateTeleport Lambda X ∧
        gateTeleport Lambda X =
          ((1 / ((D : ℝ) * (d : ℝ)) : ℝ) : ℂ) • fromChoi (transposeChoi (choi Lambda)) X := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
