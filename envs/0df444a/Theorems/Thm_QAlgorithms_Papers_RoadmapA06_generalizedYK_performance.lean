-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA06_generalizedYK_performance
-- name    : QAlgorithms.Papers.RoadmapA06.generalizedYK_performance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:37:03.748205+00:00
-- url     : https://prove2.me/theorems/0019dc24-8078-41a8-b1fe-2533863cb808
-- title:
--   Theorem 4: Performance of the generalized YK decoder
-- statement:
--   Let $\mathcal F^{AB\to D}$ be any channel on finite registers of positive dimensions $d_A,d_B,d_D$, with fixed computational bases. The registers $R,R'$ copy $A$, and $B'$ copies $B$, including their bases. Choose any Stinespring isometry $V:AB\to ED$ and a compatible unitary $U_{\mathcal F}:ABF\to ED$ with $V=U_{\mathcal F}|0\rangle^F$ and $d_A d_B d_F=d_E d_D$. Write $\overline{\mathcal F}$ for the complementary channel derived from this same isometry, $\Phi^{AR}$ for the normalized computational-basis maximally entangled state, and $\pi^X=I_X/d_X$. Define $\omega^{RE}=\overline{\mathcal F}(\Phi^{AR}\otimes\pi^B)$ and let $\lambda_{\min}(\omega^{RE})$ be its smallest strictly positive eigenvalue.
--
--   Suppose there is a density state $\tau^E$ such that $\|\omega^{RE}-\pi^R\otimes\tau^E\|_1\le\varepsilon$. For every $0<\delta<1$ and every odd positive integer $t$ satisfying
--
--   $$
--   t\ge\left\lceil16e\sqrt{\frac{d_D}{d_B\lambda_{\min}(\omega^{RE})}}\ln\frac{2}{\delta}\right\rceil,
--   $$
--
--   there are phases $\phi_1,\ldots,\phi_t\in(-\pi,\pi]$ for the explicit generalized Yoshida–Kitaev decoder $\mathcal D_{t,\phi}^{DB'\to R'}$ of Eq. (44), with preprocessing (35) and the real two-projector QSVT (49)–(53), such that
--
--   $$
--   \Delta(\mathcal D_{t,\phi}\mid\mathcal F)=\frac12\left\|\Phi^{RR'}-(\mathrm{id}_R\otimes\mathcal D_{t,\phi})(\omega^{RDB'})\right\|_1\le\sqrt{\varepsilon}+\delta,
--   \qquad
--   \omega^{RDB'}=\mathcal F^{AB\to D}(\Phi^{AR}\otimes\Phi^{BB'}).
--   $$
--
--   The channel acts as the identity on the untouched reference $R$ and shared register $B'$ in the expression for $\omega^{RDB'}$. The same choice of phases admits an exact circuit using arbitrary single- and two-qubit unitary gates with universal positive constants $C_g,C_a$ such that
--
--   $$
--   \text{gate count}\le C_g t\left(\mathcal C(U_{\mathcal F})+\log_2\frac{d_D^2d_E}{d_B}\right),
--   \qquad
--   \text{added ancilla qubits}\le C_a\log_2\frac{d_D^2d_E}{d_B}.
--   $$
--
--   Here the standing circuit model of Section 2.1 permits only polynomially many ancillary qubits. One polynomial allowance $p\in\mathbb N[X]$ is chosen before all dimensions, channels and dilations. With $q=\lceil\log_2(d_Ed_D)\rceil$, $\mathcal C_p(U_{\mathcal F})$ is the minimum exact gate count for the chosen dilation unitary within an added-ancilla budget $p(q)$, including its input and output basis layout; the displayed $\mathcal C(U_{\mathcal F})$ denotes this cost under the common chosen allowance. Both constants are independent of the channel, dimensions, chosen dilation, errors and $t$. The decoder acts only on the receiver's $DB'$ systems and locally prepared ancillas. This supplies an explicit recovery circuit whenever decoupling holds, including unassisted communication ($d_B=1$), exact decoupling ($\varepsilon=0$), and rank-deficient states.
--
--   **Formalization Note** Finite registers are embedded in $\lceil\log_2 d\rceil$ qubits by the frozen finite-register embedding; no power-of-two dimension assumption is added. The full trace norm is used for decoupling and half that norm for recovery. The logarithm in the degree threshold is natural, as in the proof's Lambert-W estimate; qubit resource logarithms are base two. The compatible dimension identity makes the resource logarithm nonnegative. When it vanishes, the recovered register is one-dimensional and discarding the input uses zero gates and added ancillas.
-- source:
--   Explicit decoders using fixed-point amplitude amplification based on QSVT, arXiv:2405.06051v6, Theorem 4, Eqs. (45)–(48), PDF p. 12. https://arxiv.org/abs/2405.06051v6 . PDF SHA-256: 7d1817ec68951e6cf58e0f3e3621a1e940e306e0c72558aab3b527f7adcb0bb6.

import Definitions.Def_QAlgorithms_Defs_GeneralizedYK
import Definitions.Def_QAlgorithms_Papers_RoadmapA06_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.RoadmapA06




/-- Theorem 4, "Performance of the generalized YK decoder", arXiv:2405.06051v6
(5 March 2026), PDF p.12, Eqs. (45)--(48), including the right-column continuation.
The explicit decoder is frozen `ykDecoder`, Eq. (44), with preprocessing (35),
projectors (49)--(50), and the real two-projector QSVT (51)--(53) (pp.10--13).
The error is half the trace norm on the preserved maximally entangled state.
The eigenvalue is the smallest NONZERO eigenvalue; full rank is not required.
The logarithm in (46) is natural, following the Lambert-W argument on p.9;
the qubit resource logarithm is base two. The polynomial ancillary allowance
of the standing gate model (p.4) and universal gate and ancilla constants are
chosen before all instances, and the same phases have both guarantees.
The resource bounds are the joint implementation bounds (167)--(168), p.25;
one-dimensional output is retained (discarding the input costs zero gates).
Only the receiver's `DB'` systems enter the decoder's circuit realization. -/
theorem generalizedYK_performance :
    ∃ ancillaBudget : Polynomial ℕ,
    ∃ gateConstant ancillaConstant : ℝ, 0 < gateConstant ∧ 0 < ancillaConstant ∧
      ∀ (A B E D F : ℕ) [NeZero A] [NeZero B] [NeZero E] [NeZero D] [NeZero F],
      ∀ (Phi : Superop (Fin A × Fin B) (Fin D))
        (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ)
        (layout : (Fin A × Fin B) × Fin F ≃ Fin E × Fin D)
        (U : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ),
      IsChannel Phi → IsChosenDilation Phi V layout U →
      ∀ (eps delta : ℝ) (t : ℕ),
      (∃ tau : Matrix (Fin E) (Fin E) ℂ, IsDensityMatrix tau ∧
        traceNorm (decouplingState V -
          Matrix.kronecker ((A : ℂ)⁻¹ • (1 : Matrix (Fin A) (Fin A) ℂ)) tau) ≤ eps) →
      0 < delta → delta < 1 → Odd t →
      ⌈16 * Real.exp 1 *
        Real.sqrt ((D : ℝ) / ((B : ℝ) * minPositiveEigenvalue (decouplingState V))) *
        Real.log (2 / delta)⌉₊ ≤ t →
      ∃ phi : Fin t → ℝ,
        (∀ j, -Real.pi < phi j ∧ phi j ≤ Real.pi) ∧
        recoveryError V (ykDecoder V phi) ≤ Real.sqrt eps + delta ∧
        ∃ unitaryGates : ℕ,
          dilationGateComplexity ancillaBudget layout U = (unitaryGates : ℕ∞) ∧
          ∃ decoderCircuit : ChannelCircuit (D * B) A,
            ExactChannelRealization
              (fun X => ykDecoder V phi (X.submatrix finProdFinEquiv finProdFinEquiv))
              decoderCircuit ∧
            (decoderCircuit.circuit.size : ℝ) ≤ gateConstant * (t : ℝ) *
              ((unitaryGates : ℝ) + Real.logb 2 ((D : ℝ) ^ 2 * (E : ℝ) / (B : ℝ))) ∧
            (decoderCircuit.added : ℝ) ≤
              ancillaConstant * Real.logb 2 ((D : ℝ) ^ 2 * (E : ℝ) / (B : ℝ)) := by sorry

end QAlgorithms.Papers.RoadmapA06
