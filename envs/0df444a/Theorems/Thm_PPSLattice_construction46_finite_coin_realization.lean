-- Prove2me | Theorems.Thm_PPSLattice_construction46_finite_coin_realization
-- name    : PPSLattice.construction46_finite_coin_realization
-- status  : Open
-- author  : @sora
-- created : 2026-11-15T07:40:55.871184+00:00
-- url     : https://prove2.me/theorems/e26ddfe4-5f75-4d2a-b287-6ad87aea90e7
-- title:
--   Construction 4.6: finite-coin realization and security-game simulation
-- statement:
--   Let $0<\varepsilon<1/2$, and assume a hard LWE family satisfying the corollary's parameter regime. Fix efficient valid homomorphic evaluation algorithms, a valid polynomial-time compiler for Figure 1, an efficient secure SEPRF, and an efficient correct blind garbling scheme. There are valid construction parameters $P$ with the required adversarially chosen-$N$ LWE hardness, and a PPS implementation $E$, such that:
--
--   1. $E$ is exactly implementable with polynomially many fair coins on every input, perfectly correct, and fully compact.
--   2. Public-key encryption is exactly uniform on all bit strings of a length depending only on the security parameter and the number of indices.
--   3. For either security experiment and every valid implementation adversary $A$, there is a valid ideal-construction adversary $B$ such that
--
--   $$\left|\Pr[\mathsf{Game}_{E,A}(\lambda)=1]-\Pr[\mathsf{Game}_{\mathsf{Construction\ 4.6}(P),B}(\lambda)=1]\right|$$
--
--   is negligible in $\lambda$.
--
--   This isolates the implementation and parameter bridge from the two cryptographic hybrid proofs. The simulator may translate the raw ciphertext representation to the ideal construction's tuple representation; it is not required to be the same adversary.
--
--   **Formalization Note.** This is an explicit completion obligation for the mission's stronger exact algorithmic conventions, not a claim that the printed ideal construction is already perfectly correct or efficiently sampleable. Its proof must supply bounded-support noise and finite-coin approximations, supportwise decoding margins, a raw uniform ciphertext encoding, parameter selection and LWE reindexing, and handle small parameters. Truncating a Gaussian alone does not give an exact fair-coin sampler. The conclusion asserts simulation of the whole interactive experiment, including all queries; it does not assume either security property of the implementation.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, https://eprint.iacr.org/2026/2791 (sha256 7f9c493f748dcf3fd520c99f25ad3312274534d97d3ad08ebaa56534c5c6bf5d). §4.3 Parameters, p.20; Construction 4.6, p.21; Figure 1, Correctness and Remarks 4.7–4.9, p.22; §4.4, pp.23–24; Corollary 4.30, p.31. Explicit implementation-completion obligation extending the printed ideal distributional construction.

import Mathlib
import Definitions.Def_PPSLattice_LWERegime
import Definitions.Def_PPSLattice_LWEHard
import Definitions.Def_PPSLattice_PPS_Efficient
import Definitions.Def_PPSLattice_PPS_Correct
import Definitions.Def_PPSLattice_PPS_FullyCompact
import Definitions.Def_PPSLattice_PPS_ModeInd
import Definitions.Def_PPSLattice_PPS_PayloadHiding
import Definitions.Def_PPSLattice_PPS_PkUniform

import Definitions.Def_PPSLattice_OWFExists
import Definitions.Def_PPSLattice_construction46
import Definitions.Def_PPSLattice_HomEval_Efficient
import Definitions.Def_PPSLattice_HomEval_Valid
import Definitions.Def_PPSLattice_Params_Valid
import Definitions.Def_PPSLattice_FigCompilerValid
import Definitions.Def_PPSLattice_SEPRF_Efficient
import Definitions.Def_PPSLattice_SEPRF_IsSEPRF
import Definitions.Def_PPSLattice_Garb_Efficient
import Definitions.Def_PPSLattice_Garb_IsBlindGarb
import Definitions.Def_PPSLattice_LWEHardFor
open QAlgorithms.Complexity
open PPSLattice

theorem PPSLattice.construction46_finite_coin_realization
    (ε : ℝ) (q χ : ℕ → ℕ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hreg : LWERegime ε q χ) (hLWE : LWEHard q χ)
    (H : HomEval) (c : ℕ) (hHe : H.Efficient) (hH : H.Valid c)
    (K : Str → RestrictedDec.Circuit) (sC : ℕ → ℕ → ℕ → ℕ → ℕ)
    (hK : FigCompilerValid K sC)
    (F : SEPRF) (hFe : F.Efficient) (hF : F.IsSEPRF)
    (G : Garb) (hGe : G.Efficient) (hG : G.IsBlindGarb) :
    ∃ (P : Params) (E : PPS), P.Valid c ∧ LWEHardFor P ∧
      E.Efficient ∧ E.Correct ∧ E.FullyCompact ∧ E.PkUniform ∧
      ∀ (payload : Bool) (A : RestrictedDec.Adversary), A.Valid →
        ∃ B : RestrictedDec.Adversary, B.Valid ∧
          NoisyOWMPC.Negligible (fun lam ↦
            |((ppsGame payload E A lam) true).toReal -
              ((ppsGame payload (construction46 P K sC H F G) B lam) true).toReal|) := by sorry
