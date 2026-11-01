-- Prove2me | Theorems.Thm_RelaxRoundPoA_relaxed_payment_le
-- name    : RelaxRoundPoA.relaxed_payment_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:30.510784+00:00
-- url     : https://prove2.me/theorems/019d714b-6d77-4ec7-8b7c-9d600e5b5375
-- title:
--   §3, p.9 (fifth display) — $p'_i(b)\le\alpha\,\mathbf E[p_i(b)]$
-- statement:
--   Let $M'$ and $M$ be pay-your-bid mechanisms with finite expectations on the weight classes, and let $M$ be obtained from $M'$ through an $\alpha$-approximate oblivious rounding scheme. For every bid profile $b$ drawn from the classes and every agent $i$,
--
--   $$
--   p_i'(b)=\mathbf E\bigl[b_i(f'(b))\bigr]\ \le\ \alpha\,\mathbf E\bigl[b_i(f(b))\bigr]=\alpha\,\mathbf E\bigl[p_i(b)\bigr].
--   $$
--
--   Payments in the relaxed mechanism are at most $\alpha$ times payments after rounding; this controls the $-\mu\sum_i p_i'(b)$ term in the proof of Theorem 3′.
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - generalization: the proofs write the outcome rule as deterministic, f(b) a point → the outcome law is any probability measure on the outcome space, almost surely an exact declared welfare maximizer where exactness is assumed; reason: p.6 allows randomized outcomes and payments; a deterministic rule is the Dirac case (verification file, check (v))
--   - encoding: expectations E[v_i(f(b))], E[p_i(b)] taken to exist → ExpFinite: every member of Val i is integrable under every outcome law on profiles; reason: excludes only the cases in which the paper's expectations are undefined; a Bochner integral of a non-integrable function would be 0
--   - reading: for all w, E[w(x)] ≥ (1/α) w(x′) (p.6) → for every x′, every agent i and every w ∈ Val i: w(x′) ≤ α · E[w(x)], the expectation a lintegral; reason: p.3 says each agent is guaranteed a 1/α-fraction, and the proof of Theorem 3′ (p.9) applies the guarantee to one agent at a time; with 0 ∈ Val j for all j the total-weight form implies this one (verification file, check (iii))
--   - encoding: problem Π with outcomes Ω ⊆ Ω′; a randomized rounding scheme maps x′ to x → Ω is a set in the measurable space Ω′; the rounding is a Markov kernel R with R x′-almost every x in Ω; M's outcome law is the outcome law of M′ bound with R; reason: standard measure-theoretic form of a randomized map; measurability of the kernel is the field's standing convention
--   - generalization: the proof of Theorem 3′ has M′ solve the relaxation optimally (p.9) → exactness of M′ is not assumed; reason: this step of the proof does not use it, so the statement covers the printed case
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, proof of Theorem 3′, p.9, fifth display

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsObliviousRounding
import Definitions.Def_RelaxRoundPoA_IsRounded

open MeasureTheory ProbabilityTheory NNReal

namespace RelaxRoundPoA

/-- **Relaxed payments are at most α times rounded payments.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, §3, proof of Theorem 3′, p.9, fifth display: "To bound the terms `p'_i(b)`, we use once more
the fact that we are applying an α-approximate oblivious rounding scheme, this time to derive `f(b)`
from `f'(b)` and considering the weight function in which `w_i = b_i` for all `i`. This implies
`p'_i(b) = b_i(f'_i(b)) ≤ α E[b_i(f_i(b))] = α E[p_i(b)]`."

Let `M'` and `M` be pay-your-bid, with `M` obtained from `M'` through an α-approximate oblivious
rounding scheme. For a profile `b` drawn from `Val` and an agent `i`: `E[p'_i(b)] ≤ α E[p_i(b)]`.

**Formalization Note** The outcome of `M'` is random in general (the paper's deterministic `f'` is
the Dirac case), so `p'_i(b)` is the expected payment `E[b_i(f'(b))]`. -/
theorem relaxed_payment_le {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω')
    (hpay' : IsPayYourBid Val M') (hpay : IsPayYourBid Val M) (hfin' : ExpFinite Val M')
    (hfin : ExpFinite Val M) (hround : IsObliviousRounding Val Ω α R) (hrel : IsRounded Val M' R M)
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) :
    M'.expPay b i ≤ α * M.expPay b i := by sorry

end RelaxRoundPoA
