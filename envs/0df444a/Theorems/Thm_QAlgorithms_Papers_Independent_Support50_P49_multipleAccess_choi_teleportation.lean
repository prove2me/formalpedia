-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P49_multipleAccess_choi_teleportation
-- name    : QAlgorithms.Papers.Independent.Support50.P49.multipleAccess_choi_teleportation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-24T00:05:21.492669+00:00
-- url     : https://prove2.me/theorems/ef78aef8-84fd-4eab-9dae-08ab971c96dc
-- title:
--   Multiple-access Choi teleportation simulation
-- statement:
--   There is any positive finite number of senders and one receiver.
--
--   Let there be finitely many senders and receivers, with positive finite transmitted input dimensions $d_i$ and output dimensions $e_j$; dimension one is allowed. Let $\mathcal E$ be a completely positive trace-preserving channel on the joint input, allowing entanglement between senders. For every tuple $o$ of input Weyl labels, assume there are separate output unitaries $V_{o,j}$, fixed independently of the unknown input, satisfying
--
--   $$
--   \mathcal E(U_o\rho U_o^\dagger)=V_o\mathcal E(\rho)V_o^\dagger,
--   \qquad U_o=\bigotimes_i U_{o_i},\quad V_o=\bigotimes_jV_{o,j}
--   $$
--
--   for every normalized input $\rho$. Construct $\rho_{\mathcal E}$ by sending one half of an independent normalized maximally entangled pair from every sender through $\mathcal E$, leaving its other half with that sender. There is a fixed table of the local corrections such that the explicit teleportation protocol $\mathcal T$ has complete local Bell instruments, is trace preserving after averaging their outcomes, and satisfies
--
--   $$
--   (\operatorname{id}_R\otimes\mathcal T)(X\otimes\rho_{\mathcal E})
--   =(\operatorname{id}_R\otimes\mathcal E)(X).
--   $$
--
--   Here each sender measures its own input and resource half, broadcasts the outcome, and each receiver applies its own inverse correction; tensor factors in the displayed equation are regrouped accordingly. The equality holds for every reference system $R$ and input operator $X$, hence in particular every normal density operator entangled with an arbitrary reference. No product-input or finite reference dimension restriction is imposed.
--
--   This realizes the physical channel by LOCC using its normalized Choi resource, the simulation needed for teleportation stretching.
--
--   **Formalization Note** The finite transmitted factors permit a blockwise formula for arbitrary reference matrix kernels. Equality on all kernels is the linear-map formulation of reference-preserving channel equality, not an assignment of probabilities to unnormalized states. The local Bell bras and product inverse corrections are body-defined; their completeness is concluded, never assumed.
-- source:
--   General bounds for sender-receiver capacities in multipoint quantum communications, arXiv:1603.07262v2, PDF p. 9, §IV, Eqs.(53)–(54) and Fig.6: multiple-access teleportation simulation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P49

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8–9, Eqs.(53)–(54), Fig.6: arbitrary positive M senders.
The channel is simulated by the explicit sender-local Bell instruments and
receiver-local inverse corrections. The equality on every reference kernel
states equality of the linear maps, hence also includes all normalized inputs
entangled with arbitrary references. The resource is the computed Choi state;
no shared resource is granted to the original channel protocol. -/
theorem multipleAccess_choi_teleportation
    {m k : ℕ} (hm : 0 < m) (hk : k = 1)
    (d : Fin m → ℕ) (e : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (he : ∀ j, 0 < e j)
    (E : Superop (Register d) (Register e)) (hE : IsChannel E)
    (hcov : ProductTeleportationCovariant hd E) :
    ∃ V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ,
      CorrectionCovariance hd E V ∧
      IsDensityMatrix (normalizedChoi E) ∧
      (∀ i : Fin m, IsKrausFamily (fun o : Fin (d i) × Fin (d i) => bellBra (d i) (hd i) o)) ∧
      IsKrausFamily (simulationKraus hd V) ∧
      ∀ (R : Type) (X : Matrix (R × Register d) (R × Register d) ℂ),
        idTensorSuperop (R := R) (teleportationLOCC hd V) (attachResource X (normalizedChoi E)) =
          idTensorSuperop (R := R) E X := by sorry

end QAlgorithms.Papers.Independent.Support50.P49

end
