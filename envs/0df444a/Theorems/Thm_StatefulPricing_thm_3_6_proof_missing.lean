-- Prove2me | Theorems.Thm_StatefulPricing_thm_3_6_proof_missing
-- name    : StatefulPricing.thm_3_6_proof_missing
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:02.228727+00:00
-- url     : https://prove2.me/theorems/08cef834-adcd-4f56-9211-0b469950e347
-- title:
--   Proof of Theorem 3.6: $\mathbb E[\#\mathrm M]\le CW/\varepsilon^{CW}$
-- statement:
--   Let $\varepsilon\in(0,1)$ and let the oracle's coins be i.i.d. Bernoulli$(\varepsilon)$, where success means "post the all-$1$ price vector in this round". For every DRACC instance with bounds $C,W$, ties broken by an injective rank, every feasible target policy $\gamma$, every $1\le t_{\mathrm{init}}\le t_{\mathrm{final}}\le T$ and every initial inventory, the number $\#\mathrm M$ of Missing rounds in $[t_{\mathrm{init}},t_{\mathrm{final}}]$ is integrable and satisfies
--   $$
--   \mathbb E[\#\mathrm M]\le\frac{CW}{\varepsilon^{CW}}.
--   $$
--   Combined with the loss of at most $\varepsilon$ per Following round, this gives the chasing regret bound $\varepsilon T+CW/\varepsilon^{CW}$ behind Theorem 3.6.
--
--   Differences from the source:
--   - generalization: ties broken by the lexicographic order on $A_t$ → ties broken by an arbitrary injective rank on bundles; reason: every lexicographic order is induced by an injective rank, so the statement specializes to the source's
--   - encoding: random coins of the oracle, $\hat\lambda_{t_{\mathrm{init}}}$ an inventory vector on $A_{t_{\mathrm{init}}}$ → coins a sequence $\xi\in\{\text{true},\text{false}\}^{\mathbb N}$ under the product of Bernoulli$(\varepsilon)$ laws, $\hat\lambda_{t_{\mathrm{init}}}$ an arbitrary function $\mathbb N\to\mathbb N$; reason: the coins after $t_{\mathrm{final}}$ are never read; values off $A_{t_{\mathrm{init}}}$ are never read
--   - encoding: $\mathbb E[\#\mathrm M]$ → integrability of $\#\mathrm M$ is asserted together with the bound; reason: $\#\mathrm M$ is bounded and depends on finitely many coins, so the source's expectation exists; asserting it keeps the bound from holding through Lean's convention $\int f=0$ for non-integrable $f$
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$ → resources are a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ at every resource; reason: changes no demand set, payment or inventory
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, proof of Theorem 3.6, p.10

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **The expected number of Missing rounds** (proof of Theorem 3.6, arXiv:2005.01869v2, p.10):
"Therefore the total number #M of Missing rounds is stochastically dominated by CW times a
geometric random variable Z with parameter ε^CW. Since E[Z] = ε^−CW, it follows that
E[#M] ≤ CW/ε^CW."

For `ε ∈ (0,1)` and coins i.i.d. Bernoulli(ε) (`true`, "post the all-1 vector", with probability
`ε`), for every instance, injective rank, feasible target policy, `1 ≤ tinit ≤ tfinal ≤ T` and
initial inventory, the number of `Missing` rounds in `[tinit, tfinal]` is integrable and its
expectation is at most `C·W / ε^{C·W}`. -/
theorem thm_3_6_proof_missing {T C W : ℕ} (I : Instance T C W) (rank : Finset ℕ → ℕ)
    (hrank : Function.Injective rank) (γ : Policy) (hγ : IsFeasiblePolicy γ)
    (tinit tfinal : ℕ) (h1 : 1 ≤ tinit) (h2 : tinit ≤ tfinal) (h3 : tfinal ≤ T) (init : ℕ → ℕ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Integrable (fun ξ => ((⟨I, rank, γ, tinit, init, ξ⟩ : Chase T C W).numMissing tfinal : ℝ))
        (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false ⟨ε, hε0.le, hε1.le⟩)) ∧
    ∫ ξ, ((⟨I, rank, γ, tinit, init, ξ⟩ : Chase T C W).numMissing tfinal : ℝ)
        ∂(Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false ⟨ε, hε0.le, hε1.le⟩))
      ≤ (C * W : ℝ) / ε ^ (C * W) := by sorry

end StatefulPricing
