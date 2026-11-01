-- Prove2me | Theorems.Thm_RelaxRoundPoA_vcg_truthful
-- name    : RelaxRoundPoA.vcg_truthful
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:47.090806+00:00
-- url     : https://prove2.me/theorems/ffe22def-19f9-4d8a-b43d-883873b9bf34
-- title:
--   §3, p.8 — $M^{\mathrm{VCG}}$ is truthful
-- statement:
--   Let $M=(f,p)$ be an exact declared welfare maximizer over $F$ whose expectations are finite on the weight classes, and let $M^{\mathrm{VCG}}=(f,p^{\mathrm{VCG}})$. For every bid profile $b$ drawn from the classes, every agent $i$, every valuation $w\in\mathcal V_i$ and every alternative bid $w''\in\mathcal V_i$,
--
--   $$
--   u_i^{\mathrm{VCG}}\bigl((w'',b_{-i}),w\bigr)\ \le\ u_i^{\mathrm{VCG}}\bigl((w,b_{-i}),w\bigr).
--   $$
--
--   Reporting the true valuation maximizes an agent's expected utility in the VCG mechanism, whatever the others bid. The proof of Lemma 1 applies this with the valuation $\tfrac12v_i$.
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - generalization: the proofs write the outcome rule as deterministic, f(b) a point → the outcome law is any probability measure on the outcome space, almost surely an exact declared welfare maximizer where exactness is assumed; reason: p.6 allows randomized outcomes and payments; a deterministic rule is the Dirac case (verification file, check (v))
--   - encoding: expectations E[v_i(f(b))], E[p_i(b)] taken to exist → ExpFinite: every member of Val i is integrable under every outcome law on profiles; reason: excludes only the cases in which the paper's expectations are undefined; a Bochner integral of a non-integrable function would be 0
--   - encoding: VCG payments p^VCG, not spelled out (p.8) → Clarke pivot payment in expectation: sup_{y∈Feas} Σ_{j≠i} b_j(y) − E[Σ_{j≠i} b_j(f(b))], the sup a real sSup; reason: the non-negative, bid-bounded VCG payments the proof uses are the Clarke pivot; under exactness the sup is over a nonempty bounded set, so it is the true supremum and equals the maximum when attained
--   - generalization: M is the pay-your-bid mechanism of Lemma 1, selecting from its outcome space (p.8) → any mechanism M, pay-your-bid not assumed, exact over a set Feas ⊆ Ω′; reason: the VCG quantities use only the outcome law of M; a pay-your-bid M with Feas its outcome space is the case in the proof
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, proof of Lemma 1, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_utility
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_vcgPay
import Definitions.Def_RelaxRoundPoA_vcgMech

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **`M^VCG` is truthful.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, §3, proof of Lemma 1, p.8: "As `M^VCG` is truthful, this term is maximized by reporting the
true valuation. In other words, it can only decrease, if bidder `i` changes his bid to `b''_i`
(keeping the valuation `b'_i`)."

For an exact declared welfare maximizer `M` over `Feas`, a profile `b` drawn from `Val`, an agent
`i` with valuation `w ∈ Val i` and any other bid `w'' ∈ Val i`, agent `i`'s expected utility in the
VCG mechanism `M^VCG` is at least as large when bidding `w` as when bidding `w''` against `b_{−i}`.

**Formalization Note** The outcome rule is randomized (a deterministic rule is the Dirac case) and
`ExpFinite` makes the expectations finite. `vcgPay` is the Clarke pivot payment in expectation,
with the others' best welfare written as a supremum over `Feas`. -/
theorem vcg_truthful {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (hfin : ExpFinite Val M)
    (hexact : IsExactMaximizer Val Feas M) (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N)
    (w w'' : Ω' → ℝ≥0) (hw : w ∈ Val i) (hw'' : w'' ∈ Val i) :
    utility (vcgMech M Feas) i (Function.update b i w'') w ≤
      utility (vcgMech M Feas) i (Function.update b i w) w := by sorry

end RelaxRoundPoA
