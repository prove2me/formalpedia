-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_proposition_4_9_resolving_adoption_failures
-- name    : PermBlockchain.Transfers.proposition_4_9_resolving_adoption_failures
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:28.759227+00:00
-- url     : https://prove2.me/theorems/e78d051f-487b-4512-93be-9d2534095df5
-- title:
--   Proposition 4.9: for sufficiently large $\Delta$, a self-financing system of transfers induces an equilibrium with full adoption
-- statement:
--   **Proposition 4.9 (Resolving Adoption Failures).** For sufficiently large $\Delta$, there exists a system of transfers that overcomes adoption failures.
--
--   Here a system of transfers is a fee $\kappa$ charged to consumers for access to the blockchain information and payments $\tau_i\ge0$ to the manufacturers that adopt, and it must be self-financing:
--   $$\kappa\cdot\mu_\kappa=\sum_{i\in M}\tau_i,\qquad(14)$$
--   where $\mu_\kappa$ is the mass of consumers who pay the fee. It overcomes adoption failures if it induces an equilibrium in which every manufacturer adopts the blockchain.
--
--   Standing assumptions: $m\ge2$ manufacturers of each type; $0\le L$ and $H=L+\Delta$; $0\le l<h$; the high vendor's cost is $c_h(x)=\gamma x$ with $\gamma>0$; the low vendor's cost $c_l$ is strictly increasing and satisfies Assumption 1 (at $H=L+\Delta$); adoption costs $\chi_i>0$; the outside option has a continuous distribution $G$ supported on $[0,\infty)$.
--
--   Precisely: there is $\bar\Delta$ such that for every $\Delta>\bar\Delta$ for which Assumption 1 holds there exist $\kappa\ge0$, $\tau_i\ge0$, a manufacturer strategy profile, a belief system, a fee rule, a purchase rule and a vendor rule that form an equilibrium of the game with transfers (consistent beliefs; optimal consumer fee and purchase decisions and optimal vendor fulfilment at every history; fulfilled demand and no profitable unilateral manufacturer deviation for every type assignment), satisfy (14), and have every manufacturer adopt for every type assignment.
--
--   This is the paper's resolution of the adoption failure of Proposition 4.8: consumers gain from blockchain information but manufacturers bear its cost, and a fee on access that is passed on to adopters restores adoption once horizontal differentiation is large. In the paper's proof the transfers are $\tau_i=\chi_i$ and $\kappa=\sum_i\chi_i/G(\phi^*)$; these are part of the proof, not of the statement.
--
--   Differences from the source:
--   - reading: "an equilibrium" (not defined in the paper) → IsTransferEquilibrium: Bayes-consistent beliefs, optimal purchase and fee decisions at every history, measurable consumer rules, optimal vendors at every (Ψ, s), on-path nonnegative prices and fulfilment, no profitable unilateral manufacturer deviation; reason: the strongest notion built from the paper's agent problems (3), (4), (7), (9), (15), (16), i.e. a perfect Bayesian equilibrium; no clause is dropped
--   - reading: (9) and (15): Π(a_i, a_{−i}) := max over P_i, Ψ_i ≥ 0; adoption decided before prices (§3.2, p. 13) → a deviation changes (a_i, P_i, Ψ_i) jointly, the other manufacturers keep their on-path actions (no re-pricing after an off-path adoption profile), consumers and vendors re-optimize; reason: the literal reading of (9)/(15), and the deviation the proof checks (p. 37, where the others keep P_j = Ψ_j = Ψ_h, Ψ_l); the paper never claims a pricing equilibrium in off-path adoption subgames
--   - reading: beliefs off the equilibrium path (not specified); each consumer's own F_k → free where Bayes' rule does not apply, but always supported on the assignments that agree with what the chain revealed; one belief system shared by all consumers (it does not depend on t_k, φ_k); reason: the perfect Bayesian convention; it gives the proof's claim that a lone non-adopter's type is known to fee payers (p. 38); t_k and φ_k are independent of the manufacturers' types, so on path the shared belief is every consumer's Bayes posterior, and off path a shared belief only restricts the witness
--   - reading: a consumer buys if her utility (weakly) exceeds φ_k (p. 12); tie-breaking among manufacturers not specified → no weight on the outside option on a tie with it; ties among manufacturers split by arbitrary purchase weights; reason: the paper's "(weakly)"; mixed weights allow the split the market shares of the proof need
--   - reading: an arbitrarily large cost for not fulfilling any consumer order (p. 11) → the constraint σ_i = s_i: on path every order is fulfilled, and a deviation is admissible only if it keeps its own order fulfilled; reason: an unfulfilled deviation incurs an arbitrarily large cost and can never be profitable, so excluding it changes nothing
--   - reading: φ_k drawn from a continuous distribution G that is supported on [0, ∞) (p. 9) → a probability measure ν on ℝ with NullSingletonClass ν (no atoms) and ν (Iio 0) = 0, G = cdf ν; reason: continuity of G is the absence of atoms; full support is not meant, since Example B.1's G is constant beyond 13/4
--   - reading: a fee κ → 0 ≤ κ in the conclusion; reason: a fee is nonnegative; this only adds to the conclusion
--   - encoding: signals with accuracy α + (1 − α) a_i b_k, α = 1/2 in the main text (p. 9) → deterministic revelation of the type of every adopter to every fee payer, no other information; reason: with α = 1/2 a signal not backed by the chain is uninformative
--   - encoding: a unit measure of consumers k ∈ [0, 1] with types t_k and outside options φ_k → the population measure (uniform on {A, B}) ⊗ ν on (t, φ); demand and μ_κ are integrals of the consumers' rules, which are required measurable in φ; reason: decisions depend on G_k only, so masses of sets of consumers are these integrals; the paper takes the sets to be measurable
--   - encoding: M = {1, …, 4m}, types common knowledge in counts; results hold "whether or not manufacturers know each others' types" (p. 8) → Fin (4 * m), and every equilibrium clause, (14) and full adoption hold for every type assignment θ in Θ; reason: a profile chosen before θ that works for every θ covers both informational cases
--   - encoding: Assumption 1 item 2: c_l convex with a strictly increasing derivative; c_l strictly increasing (p. 10) → c_l has derivative c_l'(x) within [0, ∞) at every x ≥ 0, c_l' strictly increasing on [0, ∞), and c_l strictly increasing on [0, ∞); reason: convexity on [0, ∞) follows from a strictly increasing derivative; costs are only evaluated at quantities ≥ 0; strict monotonicity of c_l is the separate standing assumption of p. 10
--   - encoding: for sufficiently large Δ, H = L + Δ, under Assumption 1 → ∃ Δbar, ∀ Δ > Δbar, Assumption1 at H = L + Δ → …, with L, h, l, γ, χ, ν, c_l and m fixed before Δbar; reason: the paper views L as fixed and lets Δ vary (p. 35); Assumption 1 is a standing assumption of each instance
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §4.2, Proposition 4.9, p. 21 (PDF p. 22), with displays (14)–(16), pp. 20–21 (PDF pp. 21–22); Assumption 1, p. 28 (PDF p. 29)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_IsTransferEquilibrium
import Definitions.Def_PermBlockchain_Transfers_SelfFinancing
import Definitions.Def_PermBlockchain_Transfers_FullAdoption
import Definitions.Def_PermBlockchain_Transfers_Assumption1

namespace PermBlockchain.Transfers

/-- **Proposition 4.9 (Resolving Adoption Failures): for sufficiently large `Δ`, a self-financing system of transfers induces an equilibrium with full adoption.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §4.2, Proposition 4.9, p. 21 (PDF p. 22): "For sufficiently large ∆, there exists a system of
transfers that overcomes adoption failures." With p. 20 (PDF p. 21): "This system of transfers
consists of charging consumers a fee κ to access the information on the blockchain, and using
these fees to pay manufacturer i an amount τ_i ≥ 0. We require that the system of transfers
(κ, {τ_i}_{i∈M}) must be self-financing … κ · µκ = Σ_{i:i∈M} τ_i (14)", and p. 21: "We say that a
system of transfers overcomes adoption failures if it induces an equilibrium in which all
manufacturers adopt blockchain (i.e., a_i = 1 for all i ∈ M)."

Standing assumptions (§3, pp. 8–12; Appendix A, p. 28): `m ≥ 2`; `0 ≤ L`, `H = L + Δ`;
`0 ≤ l < h`; `c_h(x) = γx` with `γ > 0`; `c_l` strictly increasing (p. 10) and Assumption 1 at
`H = L + Δ`; adoption costs `χ_i > 0`; the outside option has a continuous distribution
`G = cdf ν` supported on `[0, ∞)`.

Conclusion: there is `Δ̄` such that for every `Δ > Δ̄` satisfying Assumption 1 there exist a fee
`κ ≥ 0`, transfers `τ_i ≥ 0`, a manufacturer strategy, a belief system, consumer fee and purchase
rules and a vendor rule forming an equilibrium (`IsTransferEquilibrium`) that is self-financing
((14)) and has every manufacturer adopt, for every type assignment.

**Formalization Note.** `Δ̄` may depend on `m, L, h, l, γ, χ, ν, c_l` but not on `Δ` ("View L as a
fixed parameter and allow ∆ to vary", p. 35). The transfers and the profile are chosen before the
type assignment, so they cannot depend on the realized types. The paper's specific transfers
(`τ_i = χ_i`, `κ = Σχ_i / G(φ*)`) and profile belong to its proof, not to the statement. -/
theorem proposition_4_9_resolving_adoption_failures {m : ℕ} (hm : 2 ≤ m)
    {L h l γ : ℝ} (hL : 0 ≤ L) (hl : 0 ≤ l) (hlh : l < h) (hγ : 0 < γ)
    (χ : Mfr m → ℝ) (hχ : ∀ i, 0 < χ i)
    (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
    [MeasureTheory.NullSingletonClass ν] (hν : ν (Set.Iio 0) = 0)
    (cl cl' : ℝ → ℝ) (hcl : StrictMonoOn cl (Set.Ici 0)) :
    ∃ Δbar : ℝ, ∀ Δ : ℝ, Δbar < Δ → Assumption1 ν γ (L + Δ) L h l cl cl' →
      ∃ (κ : ℝ) (τ : Mfr m → ℝ) (act : Strategy m) (β : BeliefSystem m) (fee : FeeRule m)
        (w : PurchaseRule m) (vend : VendorRule m),
        0 ≤ κ ∧ (∀ i, 0 ≤ τ i) ∧
        IsTransferEquilibrium ν (L + Δ) L h l γ cl χ κ τ act β fee w vend ∧
        SelfFinancing ν κ τ act fee ∧ FullAdoption act := by sorry

end PermBlockchain.Transfers
