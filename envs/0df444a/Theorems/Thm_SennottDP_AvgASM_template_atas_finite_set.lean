-- Prove2me | Theorems.Thm_SennottDP_AvgASM_template_atas_finite_set
-- name    : SennottDP.AvgASM.template_atas_finite_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T09:51:05.690986+00:00
-- url     : https://prove2.me/theorems/d5f8ebc1-1758-4cb2-9c1b-df622e999e8d
-- title:
--   Proposition 8.2.3 — an ATAS sending excess probability to a finite set satisfies (AC)
-- statement:
--   Let $(\Delta_N)$ be an approximating sequence for the MDC $\Delta$ and assume that:
--   1. there is a $z$ standard policy $d$ for $\Delta$, with (constant) average cost $J_d$;
--   2. for some $\varepsilon>0$ the set $D=\{i\mid C(i,a)\le J_d+\varepsilon\text{ for some }a\}$ is finite;
--   3. some stationary policy $g$ for $\Delta$ induces a Markov chain with a positive recurrent class $R_g\supseteq D\cup\{z\}$ with finite average cost;
--   4. if $e$ is an average cost optimal stationary policy for $\Delta$, the Markov chain induced by $e$ has a single positive recurrent class, which contains $z$;
--   5. the AS is an ATAS that sends excess probability to $D\cup\{z\}$;
--   6. every stationary policy for $\Delta_N$ induces a unichain Markov chain with aperiodic positive recurrent class containing $z$.
--
--   Then the value iteration algorithm and the (AC) assumptions hold for
--   $$r^N(i)=\lim_{n\to\infty}\big(v^N_n(i)-v^N_n(z)\big).$$
--
--   This gives a verification route that needs no monotonicity of the value functions, only a finite set of cheap states.
--
--   **Formalization Note** $J_d$ is the average cost of the chain induced by $d$ started at $z$ (a $z$ standard chain has constant average cost). Hypothesis 4 is stated as "every positive recurrent class of the chain induced by an optimal $e$ contains $z$"; the existence of such a class is a claim the book proves, not an assumption.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 174–175, Proposition 8.2.3

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Proposition 8.2.3** (Sennott 1999, pp. 174–175). Assume that
(i) `d` is a `z` standard policy for `Δ`, with (constant) average cost `J_d`;
(ii) for some `ε > 0` the set `D = {i | C(i, a) ≤ J_d + ε for some a}` is finite;
(iii) some stationary policy `g` for `Δ` induces an MC with a positive recurrent class
`R_g ⊇ D ∪ {z}` with finite average cost;
(iv) for every average cost optimal stationary policy `e` for `Δ`, every positive recurrent class
of the MC induced by `e` contains `z` (so that there is a single one, containing `z`);
(v) the AS `(Δ_N)` is an ATAS that sends excess probability to `D ∪ {z}`;
(vi) every stationary policy for `Δ_N` induces a unichain MC with aperiodic positive recurrent
class containing `z`.
Then the VIA and the (AC) assumptions hold for `r^N(i) = lim_{n→∞} (v^N_n(i) − v^N_n(z))`. -/
theorem template_atas_finite_set {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (z : S) (d : StationaryPolicy M)
    (hd : IsStandard d.chain d.cost z)
    (ε : ℝ) (hε : 0 < ε)
    (hD : {i : S | ∃ a ∈ M.A i,
      (M.C i a : ℝ≥0∞) ≤ chainAvgCost d.chain d.cost z + ENNReal.ofReal ε}.Finite)
    (hg : ∃ (g : StationaryPolicy M) (Rg : Set S), IsPosRecClass g.chain Rg ∧
      {i : S | ∃ a ∈ M.A i,
        (M.C i a : ℝ≥0∞) ≤ chainAvgCost d.chain d.cost z + ENNReal.ofReal ε} ∪ {z} ⊆ Rg ∧
      ∀ i ∈ Rg, chainAvgCost g.chain g.cost i < ⊤)
    (hopt : ∀ e : StationaryPolicy M, IsAverageOptimal e.toPolicy →
      ∀ R, IsPosRecClass e.chain R → z ∈ R)
    (hATAS : ∃ q, AS.IsATASWith q ∧ AS.SendsExcessTo q
      ({i : S | ∃ a ∈ M.A i,
        (M.C i a : ℝ≥0∞) ≤ chainAvgCost d.chain d.cost z + ENNReal.ofReal ε} ∪ {z}))
    (hunichain : ∀ N (hN : AS.N₀ ≤ N), ∃ hz : z ∈ AS.SN N,
      ∀ e : StationaryPolicy (AS.toMDC N hN), IsUnichainAperiodicWith e.chain ⟨z, hz⟩) :
    AS.VIAAndAC z := by sorry

end SennottDP.AvgASM
