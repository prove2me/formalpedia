-- Prove2me | Theorems.Thm_SkipFreeFluct_MBI_lemma_5_1
-- name    : SkipFreeFluct.MBI.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:41.551999+00:00
-- url     : https://prove2.me/theorems/30ec4ca6-6396-4442-aa7e-6cbf4e789a5a
-- title:
--   Lemma 5.1, pp. 12–13 — generating functions of ∆W, W, κ, π, ϖ: (1−s)/ψ, 1/ψ, φ/ψ, exp(±∫₀ˢ φ/ψ)
-- statement:
--   Let $(\alpha,\mu,p,\beta,\nu,q)$ be MBI parameters, with mechanisms $\psi,\phi$ and $s_0=\inf\{s>0:\psi(s)=0\}$. Let $\bar\mu,\bar\nu$ be the tails of $\mu,\nu$ and define recursively $\Delta W(0)=\frac1{\alpha\mu(0)}$,
--   $$\Delta W(k+1)=\frac1{\mu(0)}\sum_{j=0}^k\Delta W(j)\Big(\bar\mu(k-j+1)+\frac p\alpha\Big),$$
--   $W(k)=\sum_{j=0}^k\Delta W(j)$, $\kappa(k)=\beta(\Delta W\star\bar\nu)(k)+qW(k)$, $\pi(0)=\varpi(0)=1$, $\pi(k+1)=\frac1{k+1}(\pi\star\kappa)(k)$, $\varpi(k+1)=-\frac1{k+1}(\varpi\star\kappa)(k)$.
--
--   Then $\Delta W$, $W$, $\kappa$ and $\pi$ are nonnegative, and for $s\in[0,s_0)$ the generating functions converge with
--   $$\Delta W^*[s]=\frac{1-s}{\psi(s)},\quad W^*[s]=\frac1{\psi(s)},\quad \kappa^*[s]=\frac{\phi(s)}{\psi(s)},\quad \pi^*[s]=e^{\int_0^s\frac{\phi(u)}{\psi(u)}du},\quad \varpi^*[s]=e^{-\int_0^s\frac{\phi(u)}{\psi(u)}du}.$$
--
--   These sequences are the discrete analogues of scale functions; every identity of Theorem 5.4 is written in terms of them.
--
--   Differences from the source:
--   - encoding: parameter constraints of p. 12 (α > 0, µ, ν probability measures, µ(0) > 0, µ(1) = 0, p, β, q ≥ 0) → MBIParams.Valid, with HasSum µ 1, HasSum ν 1 and ν(0) = 0; reason: same constraints
--   - encoding: GF identities f*[s] = F(s) → HasSum (k ↦ f(k) s^k) (F(s)); reason: the generating function is the sum of this series
--   - encoding: '∆W : E → [0, ∞)', 'W, κ : E → [0, ∞)', 'the nonnegative measure π' → nonnegativity conclusion clauses; reason: the codomain claims of the lemma, stated as conclusions
-- source:
--   Loeffen, Patie, Wang, Fluctuation Theory of Continuous-Time, Skip-Free Downward Markov Chains with Applications to Branching Processes with Immigration, arXiv:2208.14425v1, pp. 12–13, Lemma 5.1

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
open scoped ENNReal Topology
open Filter MeasureTheory

namespace SkipFreeFluct.MBI

/-- Lemma 5.1, pp. 12–13. For an MBI with parameters `(α, µ, p, β, ν, q)`, the sequences `∆W`,
`W`, `κ`, `π` are nonnegative, and their generating functions and that of `ϖ` are, for
`s ∈ [0, s₀)`:
`∆W*[s] = (1 - s)/ψ(s)`, `W*[s] = 1/ψ(s)`, `κ*[s] = φ(s)/ψ(s)`,
`π*[s] = exp(∫_0^s φ(u)/ψ(u) du)`, `ϖ*[s] = exp(-∫_0^s φ(u)/ψ(u) du)`. -/
theorem lemma_5_1 (P : MBIParams) (hP : P.Valid) :
    (∀ k : ℕ, 0 ≤ dW P k ∧ 0 ≤ W P k ∧ 0 ≤ kappa P k ∧ 0 ≤ piSeq P k) ∧
    ∀ s ∈ Set.Ico 0 (s0 P),
      HasSum (fun k : ℕ => dW P k * s ^ k) ((1 - s) / psi P s) ∧
      HasSum (fun k : ℕ => W P k * s ^ k) (1 / psi P s) ∧
      HasSum (fun k : ℕ => kappa P k * s ^ k) (phiImm P s / psi P s) ∧
      HasSum (fun k : ℕ => piSeq P k * s ^ k)
        (Real.exp (∫ u in (0 : ℝ)..s, phiImm P u / psi P u)) ∧
      HasSum (fun k : ℕ => varpi P k * s ^ k)
        (Real.exp (-∫ u in (0 : ℝ)..s, phiImm P u / psi P u)) := by sorry

end SkipFreeFluct.MBI
