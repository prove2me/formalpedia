-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapE07_quantumExpander_adversarial_decoding
-- name    : QAlgorithms.Papers.RoadmapE07.quantumExpander_adversarial_decoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:33:05.693967+00:00
-- url     : https://prove2.me/theorems/e6b00f2d-ad73-47bd-91c1-6385f1ef7be6
-- title:
--   Quantum expander codes: linear-time adversarial decoding
-- statement:
--   Fix positive integer degrees $\Delta_A,\Delta_B$ and positive real constants $\gamma_A,\delta_A,\gamma_B,\delta_B$, with $\delta_A,\delta_B<1/6$. There are a deterministic classical decoder, a constant $C>0$, and an integer $n_0$, all chosen before the graph sizes and inputs, with the following properties.
--
--   Let $G=(A\sqcup B,E)$ be any finite simple bipartite graph with $1\le n_B=|B|\le n_A=|A|$, left degree $\Delta_A$ and right degree $\Delta_B$. For every $S\subseteq A$ with $|S|\le\gamma_A n_A$, require $|\Gamma(S)|\ge(1-\delta_A)\Delta_A|S|$, where $\Gamma(S)$ denotes its neighboring vertices. Require the corresponding right expansion for every $S\subseteq B$ with $|S|\le\gamma_B n_B$.
--
--   Form the self hypergraph-product CSS code on the tagged coordinates $Q=(A\times A)\sqcup(B\times B)$, of length $n=n_A^2+n_B^2$. Write $H$ for the binary incidence matrix with rows $B$ and columns $A$, and set $H_X=[I_A\otimes H\mid H^{\mathsf T}\otimes I_B]$, $H_Z=[H\otimes I_A\mid I_B\otimes H^{\mathsf T}]$. Let $R_X$ and $R_Z$ be their respective binary row spaces.
--
--   On every syndrome input, the decoder terminates and realizes the Section 3 small-set-flip algorithm, treating the two components independently. Each step flips a nonempty subset of an opposite generator's support, strictly reduces syndrome weight, and maximizes the decrease divided by the number of flipped coordinates. The deterministic implementation fixes its choices among the finitely many tied candidates. A zero syndrome returns the accumulated correction; a nonzero syndrome with no improving flip returns failure. Whenever $n\ge n_0$, its total uniform-cost word-machine instruction count, together with the cost of loading its adjacency-list and syndrome input, is at most $Cn$.
--
--   For every binary error pair $e=(e_X,e_Z)$ on $Q$, let $w(e)$ count coordinates on which at least one component is nonzero. If
--
--   $$
--   w(e)<w_0:=\frac{\min(\gamma_A n_A,\gamma_B n_B)}{3(1+\Delta_B)},
--   $$
--
--   then on the exact syndrome $(H_Xe_X,H_Ze_Z)$ the decoder returns a correction $(c_X,c_Z)$ satisfying
--
--   $$
--   c_X+e_X\in R_Z,\qquad c_Z+e_Z\in R_X.
--   $$
--
--   Correctness holds at every admissible finite size. This is an exact adversarial decoding guarantee for the associated quantum code, with linear classical runtime when degrees are fixed.
--
--   **Formalization Note** The positive-degree, nonempty-part convention used in the paper's proof is explicit. Equation (6)'s mixed coordinate names are read as the supports of the $H_X$ rows fixed by Equation (1) and the incidence formulas. These source clarifications are disclosed for independent moderation; the strict threshold and all constants in it are unchanged. Runtime and realization are conclusions about an executable classical machine; no progress or minimum-distance assertion is a hypothesis.
-- source:
--   Quantum Expander Codes, arXiv:1504.00822v1, Theorem 2, PDF p. 6. https://arxiv.org/abs/1504.00822v1 . PDF SHA-256: 7bee85ff4f715166768f162007d731437073f739383c752a11a502c897f4feaf.

import Definitions.Def_QAlgorithms_Defs_ClassicalDecoderMachines
import Definitions.Def_QAlgorithms_Papers_RoadmapE07_Model
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapE07

open QAlgorithms.ExpanderCodes

attribute [local instance] Classical.propDecidable



/-- Theorem 2 (arXiv:1504.00822v1, PDF p.6, printed p.5): for fixed positive degrees
and positive left/right expansion constants with deltaA, deltaB < 1/6, a classical machine
implements the maximum-ratio small-set-flip decoder in linear uniform-cost time and corrects
every error whose union-support weight is strictly below
`min (gammaA * nA) (gammaB * nB) / (3 * (1 + degreeB))`.

The machine and runtime constants precede all graph sizes, graphs, syndromes and errors.
Executed instructions count initialization, local searches, candidate maintenance and output;
input length additionally charges loading graph adjacency lists and syndrome. Termination
and realization hold on every syndrome; correctness holds at all admissible sizes.
The deterministic machine fixes its finite choices among maximal-ratio candidates.
No progress, robustness, critical-generator or distance guarantee is a hypothesis.

Source-domain clarification: positive degrees/nonempty parts make explicit the convention
used when Appendix A chooses an edge and Appendix B divides by degrees. Allowing zero
degrees makes the printed claim false. No strict degree inequality is assumed. Equation (6)'s
coordinate correction is recorded in `IsDecoderTrace`. Both clarifications require independent
moderation; the theorem's threshold is unchanged. -/
theorem quantumExpander_adversarial_decoding
    (degreeA degreeB : ℕ) (hdegreeA : 0 < degreeA) (hdegreeB : 0 < degreeB)
    (gammaA deltaA gammaB deltaB : ℝ)
    (hgammaA : 0 < gammaA) (hdeltaA : 0 < deltaA)
    (hgammaB : 0 < gammaB) (hdeltaB : 0 < deltaB)
    (hdeltaA_lt : deltaA < 1 / 6) (hdeltaB_lt : deltaB < 1 / 6) :
    ∃ (decoder : DecoderImplementation) (C : ℝ), 0 < C ∧ ∃ n0 : ℕ,
      ∀ (nA nB : ℕ) (G : BipartiteData nA nB),
        G.degreeA = degreeA → G.degreeB = degreeB →
        LeftRightExpanding G gammaA deltaA gammaB deltaB →
        ∀ s : ((Fin nA × Fin nB) → ZMod 2) × ((Fin nB × Fin nA) → ZMod 2),
          ∃ fuel : ℕ,
            let input := decoderInput G s
            let result := decoderExecution decoder input fuel
            result.halted.isSome ∧
              IsDecoderTrace G s (decoderOutput nA nB result) ∧
              (n0 ≤ nA ^ 2 + nB ^ 2 →
                ((input.length + result.steps : ℕ) : ℝ) ≤ C * ((nA ^ 2 + nB ^ 2 : ℕ) : ℝ)) ∧
              ∀ e : Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB)),
                syndrome G e = s →
                (errorWeight e : ℝ) <
                  min (gammaA * (nA : ℝ)) (gammaB * (nB : ℝ)) /
                    (3 * (1 + (degreeB : ℝ))) →
                DecodingSuccess G e (decoderOutput nA nB result) := by sorry

end QAlgorithms.Papers.RoadmapE07
