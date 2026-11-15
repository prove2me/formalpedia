-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_Supplement_corollary_2_11
-- name    : PassiveAdiabaticFT.Thermal.Supplement.corollary_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:01:22.128566+00:00
-- url     : https://prove2.me/theorems/1b2bd943-364a-4367-8cd4-88c1f165563e
-- title:
--   Corollary 2.11 — relations between the two self-correction conditions
-- statement:
--   Let $(C_i)$ be any family of stabilizer codes with block lengths $n_i\to\infty$, at least one encoded qubit per code, and $m_i=O(n_i)$ stabilizer checks. Fix penalty $J>0$ and inverse temperature $\beta>0$, both independent of $i$. Write $\Delta_i$ for the logical energy barrier and $\delta_i$ for the maximum energy change caused by a single-qubit Pauli. All three conclusions hold:
--
--   1. For every $c_1>0$, if there are decoders whose canonical bad sets satisfy the commutator condition and $p_i=\pi_{\beta,i}(B_{\mathrm{dec},i})\le A e^{-a n_i^{c_1}}$ eventually for fixed $A,a>0$, then
--      $$\Delta_i=\Omega\left(\frac{n_i^{c_1}}{\log n_i}\right).$$
--   2. If this rare-syndrome property holds with $c_1=1$, then the sharper conclusion is
--      $$\Delta_i=\Omega(n_i).$$
--   3. Conversely, if some fixed $\delta_*\ge0$ and $c'>0$ satisfy $\delta_i\le\delta_*$ and $\Delta_i\ge Jc'n_i$ eventually, and
--      $$J\beta>\frac{2\ln 2}{c'},$$
--      then there are thermally protected decoders with exponent $1$: their admissible canonical bad sets have $p_i\le A e^{-a n_i}$ eventually for some fixed $A,a>0$.
--
--   Every asymptotic lower-bound coefficient is positive and independent of $i$. No bounded check degree, geometric locality, independent-check, CSS or fixed-logical-dimension assumption is imposed. This is the complete comparison theorem, also stated as Theorem 1.9 in the introduction.
--
--   Differences from the source:
--   - encoding: a code family with unbounded available block lengths and asymptotic O and Omega notation → a cofinal sequence n_i with explicit positive coefficients and eventual index thresholds; reason: this represents arbitrary available block lengths without requiring a code at every integer size; all constants precede the index quantifier
--   - encoding: n^c/log n in an asymptotic claim → real powers and real logarithms, with n_i ≥ 2 after the threshold; reason: cofinality supplies this threshold and prevents totalized division or logarithm from changing a small-size instance
--   - encoding: thermal protection and the canonical probability p_n = pi_beta(union D_alpha) → rareBad includes the commutator condition for Bdec and existential decoders at every sufficiently large index; reason: the published Lemma 2.4 makes Bdec admissible and minimal; the existence and decay are conclusions in clause 3, not hypotheses
-- source:
--   Arsalan Motamedi, Peter Love, STOC 2027 submission #1144 (October 2026), Corollary 2.11, pp. 18–19, (2.36)–(2.39); formal version of Theorem 1.9, p. 11.

import Definitions.Def_PassiveAdiabaticFT_Thermal_Supplement_Families

set_option autoImplicit false

namespace PassiveAdiabaticFT.Thermal.Supplement

/-- Corollary 2.11, pp. 18-19 (the formal version of Theorem 1.9): all three clauses.
All asymptotic constants are independent of the family index; J and beta are fixed positive
reals. The converse needs only bounded single-error energy change delta, not bounded degree.
The strict temperature threshold and the factor J in the linear barrier are unchanged. -/
theorem corollary_2_11 (F : CodeFamily) (J β : ℝ)
    (hJ : 0 < J) (hβ : 0 < β) (hm : linearChecks F) :
    (∀ c : ℝ, 0 < c → rareBad F J β c →
      barrierOmega F J (fun n => (n : ℝ) ^ c / Real.log (n : ℝ))) ∧
    (rareBad F J β 1 → barrierOmega F J (fun n => (n : ℝ))) ∧
    (∀ δstar c' : ℝ, 0 ≤ δstar → 0 < c' →
      (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
        (F.code i).delta J ≤ δstar ∧ J * c' * (F.n i : ℝ) ≤ (F.code i).barrier J) →
      2 * Real.log 2 / c' < J * β → rareBad F J β 1) := by sorry

end PassiveAdiabaticFT.Thermal.Supplement
