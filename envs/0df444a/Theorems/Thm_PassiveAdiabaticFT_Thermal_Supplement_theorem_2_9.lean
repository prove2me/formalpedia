-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_Supplement_theorem_2_9
-- name    : PassiveAdiabaticFT.Thermal.Supplement.theorem_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:00:42.207252+00:00
-- url     : https://prove2.me/theorems/d8e4f601-aced-4e74-b75d-8b4b4ac69800
-- title:
--   Theorem 2.9 — rare syndromes require an energy barrier
-- statement:
--   Let $C$ be a stabilizer code on $n$ qubits encoding $k\ge1$ logical qubits, with $m$ possibly dependent stabilizer checks, penalty $J>0$, and syndrome Gibbs distribution $\pi_\beta$ at inverse temperature $\beta\ge0$. Let $D$ be any Pauli decoder and let $B\subseteq\Omega$ satisfy condition 1 of Definition 1.1: every dressed logical operator commutes with every single-qubit Pauli on the complement of $B$. Let $\Delta_n$ be the logical energy barrier and $r_n=\Delta_n/(2J)$ its integer count of violated checks. Then
--
--   $$\pi_\beta(B)\ge\frac{e^{-\beta\Delta_n}}{|\Omega_{\le\Delta_n}|},\qquad
--   \log\frac1{\pi_\beta(B)}\le\beta\Delta_n+\log\left(\sum_{j=0}^{r_n}\binom mj\right).$$
--
--   The denominator and $\pi_\beta(B)$ are strictly positive. The sum is inclusive and counts all binary check strings, including inadmissible ones; the denominator counts only acceptable syndromes. Zero barrier is allowed and forces $\pi_\beta(B)=1$. No rarity or asymptotic assumption is required. The result is the finite-size input for comparing the two self-correction conditions.
--
--   Differences from the source:
--   - encoding: syndromes and integer r_n = Delta_n/(2J) → functions Fin m → ZMod 2 and r_n = C.barrierCount; reason: the published barrier is exactly 2J times this integer; the sum uses range (r_n+1) to include both endpoints
--   - encoding: the positive denominator and bad-set probability implicit in (2.27)–(2.28) → their strict positivity is also asserted as a conclusion; reason: these follow from the code setting and the covering argument; no positivity hypothesis or zero-barrier exclusion is added
-- source:
--   Arsalan Motamedi, Peter Love, STOC 2027 submission #1144 (October 2026), Theorem 2.9, p. 17, (2.27)–(2.28), proof pp. 17–18.

import Definitions.Def_PassiveAdiabaticFT_Thermal_Supplement_LowEnergy

set_option autoImplicit false

namespace PassiveAdiabaticFT.Thermal.Supplement

/-- Theorem 2.9, p. 17, equations (2.27)-(2.28), with the standing code convention k >= 1.
Both finite-size inequalities hold for every decoder and every admissible bad set.
The strict positivity clauses expose the well-defined denominators/logarithms; they are
conclusions, not additional assumptions. The barrier is allowed to be zero.
The integer r_n is the published barrierCount, so Delta_n = 2 J r_n. -/
theorem theorem_2_9 {n : ℕ} (C : StabCode n) (D : PauliDecoder C)
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 ≤ β)
    (B : Finset (Fin C.m → ZMod 2)) (hB : D.BadSetCondition B) :
    0 < ((omegaLe C J (C.barrier J)).card : ℝ) ∧
    0 < C.gibbsSet J β B ∧
    Real.exp (-(β * C.barrier J)) / ((omegaLe C J (C.barrier J)).card : ℝ) ≤
      C.gibbsSet J β B ∧
    Real.log (1 / C.gibbsSet J β B) ≤ β * C.barrier J +
      Real.log (∑ j ∈ Finset.range (C.barrierCount + 1), (Nat.choose C.m j : ℝ)) := by sorry

end PassiveAdiabaticFT.Thermal.Supplement
