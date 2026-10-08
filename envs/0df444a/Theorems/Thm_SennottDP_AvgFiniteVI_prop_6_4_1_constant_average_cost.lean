-- Prove2me | Theorems.Thm_SennottDP_AvgFiniteVI_prop_6_4_1_constant_average_cost
-- name    : SennottDP.AvgFiniteVI.prop_6_4_1_constant_average_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:31:34.344802+00:00
-- url     : https://prove2.me/theorems/250cfd43-686a-4282-80c8-838090c38a74
-- title:
--   Proposition 6.4.1 — conditions under which the minimum average cost is constant
-- statement:
--   Let $\Delta$ be an MDC with a finite nonempty state space $S$, and let $f$ be a stationary policy that is $\alpha$ discount optimal for every $\alpha \in (\alpha_0,1)$, for some $\alpha_0 \in (0,1)$ (Proposition 6.2.3). Consider:
--
--   1. (i) every stationary policy induces a unichain Markov chain;
--   2. (ii) $f$ induces a unichain Markov chain;
--   3. (iii) there exist $z \in S$ and a finite $L$ with $|V_\alpha(i) - V_\alpha(z)| \le L$ for all $i \in S$, $\alpha \in (0,1)$;
--   4. (iv) for every $x \in S$ there is a finite $L$ with $|V_\alpha(i) - V_\alpha(x)| \le L$ for all $i \in S$, $\alpha \in (0,1)$;
--   5. (v) for all states $i \ne j$ there is a stationary policy $e(i,j)$ under which $i$ leads to $j$;
--   6. (*) $J(i) \equiv J$ for $i \in S$.
--
--   Then
--   $$\text{(i)} \Rightarrow \text{(ii)} \Rightarrow \text{(iii)} \Leftrightarrow \text{(iv)} \Leftrightarrow (*), \qquad \text{(v)} \Rightarrow (*).$$
--
--   The proposition gives checkable sufficient conditions (chain structure, communication) for a constant minimum average cost, the hypothesis of the rest of the chapter.
--
--   **Formalization Note** The seven implications are stated separately; they are not a list of equivalent statements. $V_\alpha$ is converted to a real number (it is finite for finite $S$ and $\alpha<1$).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 108, Proposition 6.4.1, Eq. (6.26)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_ACOE

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal

/-- Proposition 6.4.1 (Sennott, p. 108). Let `S` be finite (and nonempty), and let `f`, `α₀` be as
in Proposition 6.2.3 (`f` is `α` discount optimal for every `α ∈ (α₀,1)`). Consider
(i) every stationary policy induces a unichain Markov chain;
(ii) `f` induces a unichain Markov chain;
(iii) there exist `z ∈ S` and a finite `L` with `|V_α(i) − V_α(z)| ≤ L` for `i ∈ S`, `α ∈ (0,1)`;
(iv) given `x ∈ S`, there is a finite `L` with `|V_α(i) − V_α(x)| ≤ L` for `i ∈ S`, `α ∈ (0,1)`;
(v) given states `i ≠ j`, some stationary policy `e(i,j)` has `i` leading to `j`;
(*) `J(i) ≡ J` for `i ∈ S`.
Then (i) ⇒ (ii) ⇒ (iii) ⇔ (iv) ⇔ (*), and (v) ⇒ (*) (6.26). -/
theorem prop_6_4_1_constant_average_cost {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    (M : MDC S Act) (f : StationaryPolicy M) (α₀ : ℝ) (hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α) :
    let P1 : Prop := ∀ e : StationaryPolicy M, IsUnichain (inducedChain M e)
    let P2 : Prop := IsUnichain (inducedChain M f)
    let P3 : Prop := ∃ z : S, ∃ L : ℝ, ∀ i : S, ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      |(discValue M α i).toReal - (discValue M α z).toReal| ≤ L
    let P4 : Prop := ∀ x : S, ∃ L : ℝ, ∀ i : S, ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      |(discValue M α i).toReal - (discValue M α x).toReal| ≤ L
    let P5 : Prop := ∀ i j : S, i ≠ j → ∃ e : StationaryPolicy M, SennottDP.AvgFinite.LeadsTo (inducedChain M e) i j
    let Pstar : Prop := ∃ J : ℝ≥0∞, ∀ i : S, avgValue M i = J
    (P1 → P2) ∧ (P2 → P3) ∧ (P3 ↔ P4) ∧ (P4 ↔ Pstar) ∧ (P5 → Pstar) := by sorry

end SennottDP.AvgFiniteVI
