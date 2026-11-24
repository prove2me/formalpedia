-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_Supplement_theorem_2
-- name    : WaitTimePricing.Existence.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:41:32.43461+00:00
-- url     : https://prove2.me/theorems/254d6736-4cef-4d88-9558-2b4d630cca99
-- title:
--   Theorem 2 — optimal expected averages (corrected: counterexample to the abstract extension)
-- statement:
--   For every model satisfying the published standing assumptions, for either concrete objective, and for any Poisson arrival realization at the model's rate with its natural history, let $g=\bar g$ and $V=V^{\bar g}$ be the constructed values. The greatest-maximizer feedback (25)–(26) is measurable and its operational price process $p^*$ is admissible. Over every admissible predictable competitor,
--   $$g^*=g=G(p^*).$$
--   Every finite-horizon actual reward is integrable, its expected average lies between zero and $\lambda U'(0)C$, the competitor set is nonempty, and the attainable averages are bounded above. The greatest price maximizer exists at each state in $[0,\bar w]$.
--
--   The theorem also states an exact counterexample to the abstract extension on page 11. With $U(t)=2t-t^2/2$, $c(w)=w$, $C=\lambda=1$, set $\alpha=0$ and $v(p)=2-p$ for $0<p<1$, zero otherwise. The standing assumptions and (V1),(V2) hold, but
--   $$\nexists(g,V):\quad V\text{ is continuous and nonincreasing on }[0,\infty),\quad (g,V)\text{ solves the supremum DDEs},\quad \arg\max_{p\in[0,\Gamma(0)]}\xi(p,0)\ne\varnothing.$$
--   Thus the printed conditions do not guarantee the maximizer needed for (25). This does not weaken concrete revenue or welfare optimality or add regularity assumptions to the abstract reward class.
--
--   Differences from the source:
--   - encoding: Assumption 1 and positive arrival and service primitives → the immutable base Standing predicate, including global C³/C² extensions and λ,C>0; reason: reuse of the published model; inequalities remain on their original physical domains
--   - encoding: the Poisson jump dynamics (9) and predictable controls → strictly ordered nonexplosive arrival epochs, natural filtration and all predictable price processes, with operational arrival recursion; reason: equivalent continuous-time representation using càdlàg counts and strictly prearrival controls; regular versions are chosen on null paths
--   - generalization: g*=g=G(p*) → the same equalities plus integrability, finite-horizon bounds, feedback admissibility and greatest-maximizer attainment as conclusions; reason: these well-definedness claims follow for the concrete objectives and exclude junk real integral, liminf and supremum values
--   - correction: arbitrary rewards satisfying only (V1),(V2), with α≥0, also admit the Section 4 construction and maximizing feedback → an explicit Borel reward satisfying those conditions for which no continuous antitone supremum-DDE solution has an empty-state maximizer; reason: on 0<p<1 service is 1 and replacing p by p/2 strictly improves every positive candidate; the empty-state equation forces a positive maximum
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 19, Theorem 2, pp. 9–11, (9)–(10) and abstract reward paragraph; pp. 17–18, (25)–(26)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Definitions.Def_WaitTimePricing_Existence_Supplement_Performance

set_option autoImplicit false

namespace WaitTimePricing.Existence.Supplement
open Set MeasureTheory

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 19, Theorem 2, and p. 11, abstract reward paragraph.
Formalization Note: concrete optimality retains every predictable competitor, actual admission
rewards, and the liminf outside expectation. Integrability, boundedness, maximum attainment and
feedback admissibility are conclusions, never premises. The second conjunct refutes the printed
extension to arbitrary rewards satisfying only (V1),(V2): for the specified polynomial model and
Borel reward no continuous antitone DDE solution can have even one maximizer at the empty state. This is a
counterexample to that extension, not an added continuity assumption or a claim that the base
mission was published for arbitrary rewards. Standing uses the base global C³/C² conventions. -/
theorem theorem_2 :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (M : Model) (obj : Objective), M.Standing →
      ∀ A : Arrivals Ω, (A.rate : ℝ) = M.lam →
      let R := concreteReward M obj
      let F := feedback M R (Vbar M obj)
      let pstar := ruleProcess M A F
      (∀ w ∈ Icc 0 (wbar M), IsGreatest (priceArgmax M R (Vbar M obj) w)
        (pbar M R (Vbar M obj) w)) ∧
      Measurable F ∧ Admissible M A pstar ∧
      (∀ p : PriceProcess Ω, Admissible M A p →
        (∀ T : ℝ, 0 < T → Integrable (totalReward M R A p T) A.law) ∧
        (∀ T : ℝ, 0 < T → 0 ≤ average M R A p T ∧
          average M R A p T ≤ M.lam * deriv M.U 0 * M.C)) ∧
      (G M R A '' {p | Admissible M A p}).Nonempty ∧
      BddAbove (G M R A '' {p | Admissible M A p}) ∧
      gStar M R A = gbar M obj ∧ gbar M obj = G M R A pstar) ∧
    ((testModel 1).Standing ∧
      nonattainingReward.Conditions (testModel 1) ∧
      ¬ ∃ (g : ℝ) (V : ℝ → ℝ),
        abstractSolves (testModel 1) nonattainingReward g V ∧
        ContinuousOn V (Ici 0) ∧ AntitoneOn V (Ici 0) ∧
        (priceArgmax (testModel 1) nonattainingReward V 0).Nonempty) := by sorry

end WaitTimePricing.Existence.Supplement
