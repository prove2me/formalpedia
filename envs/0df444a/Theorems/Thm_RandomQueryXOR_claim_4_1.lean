-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_4_1
-- name    : RandomQueryXOR.claim_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:07:31.488518+00:00
-- url     : https://prove2.me/theorems/d827096d-bb60-4eac-8a7f-ac5a74085373
-- title:
--   Claim 4.1 — the gate-keeper input model costs length $4T+16\ln(1/\delta)$ and width $(T+1)2^S$
-- statement:
--   Let $P$ be a randomized branching program of length $T$ and width $2^S$ that reads independent samples $(i_t,x(i_t))$ with $i_t$ uniform on a nonempty finite index set. For every $\delta>0$ there is a randomized branching program $P'$ of length
--   $$
--   T'=\bigl\lceil 4T+16\ln(1/\delta)\bigr\rceil
--   $$
--   and width $(T+1)\cdot2^S$ that reads gate-keeper samples $(i,b,w(i))$, with $(i,b)$ uniform and $w(i)=x(i)$ if $b=1$, $\bot$ if $b=0$, and that exactly simulates $P$ with probability at least $1-\delta$: there are $q\in[0,\delta]$, independent of the input, and numbers $\nu_x\in[0,1]$ such that for every input $x$
--   $$
--   \Pr[P'(x)=1]=(1-q)\Pr[P(x)=1]+q\,\nu_x .
--   $$
--
--   The claim lets the lower-bound argument work in the gate-keeper model, where the random bits $b_j$ record which samples carried information, at the price of constant factors in length and width.
--
--   Differences from the source:
--   - generalization: T′ = O(T + log(1/δ)) and width at most O(T · 2^S) → T′ = ⌈4T + 16 ln(1/δ)⌉ and width exactly (T + 1) · 2^S; reason: these are the proof's values (pp.15–16); explicit bounds imply the printed O-bounds
--   - encoding: P′ exactly simulates P with probability at least 1 − δ → for one q ∈ [0, δ] independent of x, the output law of P′ on every x is (1 − q)·(output law of P on x) + q·ν_x; reason: the run of P′ is the run of P outside an event of probability q ≤ δ that depends only on the gate bits; a {0,1}-valued output law is given by Pr[output = 1]
--   - generalization: indices uniform over [n] → indices uniform over any nonempty finite type ι; reason: the claim specializes at ι = Fin n, n ≥ 1 (§3.1 works with n ≥ 1)
--   - encoding: a randomized branching program: a distribution D^A_n on programs with per-node distributions over outgoing edges → a probability distribution (WildeQIT.FinDist) on deterministic layered programs DetBP (2^S) _ T; reason: a run visits one node per layer, so independent per-node edge choices fold into a distribution on deterministic programs; the paper does the same in π_two step (ii)
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 4.1, p.15 (PDF p.17); constants from the proof, pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_successProb
import Definitions.Def_RandomQueryXOR_gateSuccessProb

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- Claim 4.1 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.15 = PDF p.17): "Let P be a branching program of length T and width 2^S whose
input consists of independent samples (i_1, x(i_1)), …, (i_T, x(i_T)), i_1, …, i_T are uniform over
[n]. Consider instead the distribution in which each sample is of the form (i, b, w(i)) where (i, b) is
uniform over [n] × {0, 1} independently and w(i) = x(i) if b = 1, ⊥ if b = 0. Then, for every δ > 0,
there is a branching program P′ of length T′ = O(T + log(1/δ)) and width at most O(T · 2^S) such that
P′ exactly simulates P with probability at least 1 − δ."

**Formalization Note** The O(·)'s are the proof's values (pp.15–16): length
`T′ = ⌈4T + 16 ln(1/δ)⌉` and width `(T + 1)·2^S` (states `(j, v)`). "Exactly simulates with
probability at least 1 − δ" is stated on the output law: for one `q ∈ [0, δ]` independent of the input
(the probability that fewer than `T` samples have `b = 1`), the output law of `P′` on every `x` is the
mixture `(1 − q)·(law of P(x)) + q·ν_x`; on `{0,1}`-valued outputs a law is given by
`Pr[output = 1]`. `P` and `P′` are randomized programs (distributions on deterministic programs);
`[n]` is any nonempty finite index set `ι` (the paper has `n ≥ 1`, §3.1; with no index at
all a program with `T = 0` has an output while every gate-keeper program with `T′ ≥ 1` has none). -/
theorem claim_4_1 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {S T : ℕ}
    (μ : FinDist (DetBP (2 ^ S) (ι × Bool) T)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ' : FinDist (DetBP ((T + 1) * 2 ^ S) (GateSample ι)
        ⌈4 * (T : ℝ) + 16 * Real.log (1 / δ)⌉₊),
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ δ ∧ ∃ ν : (ι → Bool) → ℝ, (∀ x, 0 ≤ ν x ∧ ν x ≤ 1) ∧
        ∀ x : ι → Bool, gateOutProb μ' x true = (1 - q) * outProb μ x true + q * ν x := by sorry

end RandomQueryXOR
