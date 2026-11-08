-- Prove2me | Theorems.Thm_PolarizedLearning_piMinus_lt_one
-- name    : PolarizedLearning.piMinus_lt_one
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:18:56.434327+00:00
-- url     : https://prove2.me/theorems/9dda77f7-f1ae-4f85-838e-d8ac23af93f1
-- title:
--   Proof of Theorem 2, Case (ii), p. ec2 — $x\le H+p(2u-1)\Rightarrow\pi^-(x)<1$, and $x\ge L+p(2u-1)\Rightarrow\pi^+(x)>0$
-- statement:
--   Fix the model parameters (in particular $p>0$ and $\epsilon>0$) and $x\in[0,1]$. Then:
--
--   1. if $x\le H+p(2u-1)$, then $$\pi^-(x)<1;$$
--   2. if $x\ge L+p(2u-1)$, then $$\pi^+(x)>0.$$
--
--   Every limit point of the consumption rate when $q=H$ satisfies the hypothesis of part 1 (it equals the mean consumption probability, which is at most $H+p(2u-1)$), so the ML beliefs never single out $\pi=1$: the uncertainty about the in-group share keeps a belief strictly below one in the ML set. Part 2 is the mirror statement for $q=L$.
--
--   Differences from the source:
--   - generalization: π⁻(x*(H)) < 1 at the single point x*(H) = H + p(2u − 1) → π⁻(x) < 1 for every x ∈ [0,1] with x ≤ H + p(2u − 1); reason: specializes at x = x*(H); every fixed point of the mean consumption map for q = H satisfies the inequality
--   - reading: 'The proof for q = L follows from symmetric argument and will be omitted' → L + p(2u − 1) ≤ x → 0 < π⁺(x); reason: the symmetric statement the q = L case needs
--   - reading: standing assumptions of pp. 8–11 (H > L, p > 0, L − p > 0, H + p < 1, u ∈ (0,1), [u−ϵ,u+ϵ] ⊆ [0,1], α > 0.5) → Params, which also requires ϵ > 0 and α < 1; reason: ϵ is called a degree of uncertainty and divided by on p. 17; the signal 'noisily reveals' quality (p. 11), and at α = 1 learning is complete (counterexample in paper.md item 3)
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, e-companion, proof of Theorem 2, Case (ii), p. ec2 (PDF 34)

import Mathlib
import Definitions.Def_PolarizedLearning_Model

namespace PolarizedLearning

/-- **Under polarization the ML beliefs never collapse onto the true quality**, Kadiyala–Shin,
*Social Learning and Content Quality under Polarization*, MSOM (2024), doi:10.1287/msom.2022.0533,
e-companion, proof of Theorem 2, Case (ii), p. ec2 (PDF 34): at `x*(H) = H + p(2u − 1)` "there
exists `π̃ < 1` and `ũ > u` such that `(π̃, ũ) ∈ B(x*(H))`. This implies that `π⁻(x*(H)) < 1`".

For `x ∈ [0,1]`:
1. if `x ≤ H + p(2u − 1)` then `π⁻(x) < 1`;
2. (the case `q = L`, omitted in the paper as symmetric) if `L + p(2u − 1) ≤ x` then
   `0 < π⁺(x)`. -/
theorem piMinus_lt_one (P : Params) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (x ≤ P.H + P.p * (2 * P.u - 1) → piMinus P x < 1) ∧
    (P.L + P.p * (2 * P.u - 1) ≤ x → 0 < piPlus P x) := by sorry

end PolarizedLearning
