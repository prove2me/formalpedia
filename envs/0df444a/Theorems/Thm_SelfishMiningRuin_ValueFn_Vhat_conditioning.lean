-- Prove2me | Theorems.Thm_SelfishMiningRuin_ValueFn_Vhat_conditioning
-- name    : SelfishMiningRuin.ValueFn.Vhat_conditioning
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T08:55:35.529904+00:00
-- url     : https://prove2.me/theorems/bd8a0626-1e36-427c-bfb6-a26e01b5b20c
-- title:
--   Conditioning identity on $(0,h)$ for the exponential-horizon value functions
-- statement:
--   Fix a cost rate $c>0$, a block reward $b>0$, a block rate $\lambda>0$, a mean horizon $t>0$, a hash share $0<p<1$ and a fork-support probability $0\le q\le1$, and let the interarrival times and marks have the joint law described by `Primitives` (i.i.d. $\mathrm{Exp}(\lambda)$ interarrival times, with independent marks $\xi\sim\mathrm{Bernoulli}(p)$ — the selfish miner found the block — and $\zeta\sim\mathrm{Bernoulli}(q)$ — the network extends the miner's branch in a fork). For a state $z\in\{0,1,0^*\}$ write $\widehat V_z(u)=\widehat V_z(u,t)$ for the exponential-horizon expected surplus under ruin (19), and $\beta=\lambda+1/t$.
--
--   Conditioning on what happens in the interval $(0,h)$ — the horizon expires first, a block is found first, or neither — gives, for every $u$ and every $0\le h\le u/c$,
--
--   $$
--   \widehat V_z(u)=e^{-\beta h}\,\widehat V_z(u-ch)+\int_0^h e^{-\beta s}\Bigl(\frac{u-cs}{t}+\lambda\sum_{x,y\in\{0,1\}}\pi(x,y)\,\widehat V_{z'(x,y)}\bigl(u-cs+b\,r_z(x,y)\bigr)\Bigr)\,ds ,
--   $$
--
--   where $\pi(x,y)=p^x(1-p)^{1-x}q^y(1-q)^{1-y}$ is the mark law, $z'(x,y)$ is the next state and $r_z(x,y)\in\{0,1,2\}$ the number of paid blocks at a discovery (the transition rules on pp. 8–9 and equation (16)).
--
--   This is the identity displayed in the proof of Proposition 2.2 (p. 6), stated there for the honest miner and used in Appendix A ("the same reasoning as in the proof of Proposition 2.2") for the three-state selfish-mining chain. Differentiating it in $h$ yields the advanced differential system (29).
--
--   **Formalization Note** The paper takes $0<h<u/c$; the identity also holds at the endpoints $h=0$ (trivially) and $h=u/c$ (the surplus is exhausted at $u/c$ if no block arrives, and $\widehat V_z(0)=0$), and the statement includes them.
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, proof of Proposition 2.2 (conditioning identity), p. 6, applied to the selfish-mining chain in Appendix A, p. 24 (derivation of (29))

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Model

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

/-- Conditioning on the interval `(0, h)` (proof of Proposition 2.2, p. 6, transferred to the
three-state chain as in Appendix A, p. 24), for every `0 ≤ h ≤ u / c`. -/
theorem Vhat_conditioning {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (W : ℕ → Ω → ℝ)
    (ξ ζ : ℕ → Ω → Bool) (lam c b t p q : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ) :
    ∀ z : St, ∀ u h : ℝ, 0 ≤ h → c * h ≤ u →
      Vhat P W ξ ζ c b u t z =
        Real.exp (-(lam + 1 / t) * h) * Vhat P W ξ ζ c b (u - c * h) t z +
        ∫ s in (0 : ℝ)..h, Real.exp (-(lam + 1 / t) * s) *
          ((u - c * s) / t + lam *
            (p * q * Vhat P W ξ ζ c b (u - c * s + b * reward z true true) t
                (step z true true) +
             p * (1 - q) * Vhat P W ξ ζ c b (u - c * s + b * reward z true false) t
                (step z true false) +
             (1 - p) * q * Vhat P W ξ ζ c b (u - c * s + b * reward z false true) t
                (step z false true) +
             (1 - p) * (1 - q) * Vhat P W ξ ζ c b (u - c * s + b * reward z false false) t
                (step z false false))) := by sorry

end SelfishMiningRuin.ValueFn
