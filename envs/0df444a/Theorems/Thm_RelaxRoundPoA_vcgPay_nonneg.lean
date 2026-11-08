-- Prove2me | Theorems.Thm_RelaxRoundPoA_vcgPay_nonneg
-- name    : RelaxRoundPoA.vcgPay_nonneg
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:50:45.367876+00:00
-- url     : https://prove2.me/theorems/8b7bab3c-affd-4847-91a9-c81fff24c4a3
-- title:
--   §3, p.8 — VCG payments are non-negative
-- statement:
--   Let $M=(f,p)$ be an exact declared welfare maximizer over the feasible set $F$ whose expectations are finite on the weight classes. Then for every bid profile $b$ drawn from the classes and every agent $i$, the expected VCG payment is non-negative:
--
--   $$
--   p_i^{\mathrm{VCG}}(b)\ge0.
--   $$
--
--   This is the first step of the proof of Lemma 1: it shows that an agent bidding $\tfrac12v_i$ in the pay-your-bid mechanism gets at least its utility in the VCG mechanism.
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
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_vcgPay

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **VCG payments are non-negative.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, §3, proof of Lemma 1, p.8: "As VCG payments are non-negative, we get
`u_i((b'_i, b_{−i}), v_i) = ½ v_i(f(b'_i, b_{−i})) = b'_i(f(b'_i, b_{−i})) ≥ b'_i(f(b'_i, b_{−i})) − p^VCG(b'_i, b_{−i})`."

For an exact declared welfare maximizer over `Feas` and a profile `b` drawn from `Val`, agent `i`'s
expected VCG payment is nonnegative.

**Formalization Note** The outcome rule is randomized (a deterministic rule is the Dirac case) and
`ExpFinite` makes the expectations finite. `vcgPay` is the Clarke pivot payment in expectation,
with the others' best welfare written as a supremum over `Feas`. -/
theorem vcgPay_nonneg {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (hfin : ExpFinite Val M)
    (hexact : IsExactMaximizer Val Feas M) (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) :
    0 ≤ vcgPay M Feas b i := by sorry

end RelaxRoundPoA
