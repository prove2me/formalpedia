-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_lemma_3_2
-- name    : QuasilinearAG.Encoding.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:50.179351+00:00
-- url     : https://prove2.me/theorems/51d3e040-63e2-452e-96b3-612a75e29c88
-- title:
--   Lemma 3.2 — degree-paid rounding: after $\kappa$ extractions the pole at $P\mid t$ is at most $\lfloor a/Q_*\rfloor+e_P-1$
-- statement:
--   In the height-$h$ second Garcia–Stichtenoth tower over $k=\mathbb F_{q^2}$ ($q=p^s>2$, $h\ge1$), with $t=x_0^q+x_0$, $\kappa=\lceil\log_q h\rceil+1$, $Q_*=q^\kappa$ and $e_P$ the ramification index over $k(x_0)$:
--
--   1. if $P\mid t$ and $a\ge0$ is an initial pole bound for $f$ at $P$ ($\operatorname{ord}_P f\ge-a$), then after $\kappa$ extractions the effective pole is bounded by $\lfloor a/Q_*\rfloor+e_P-1$ (3.12), i.e. $\operatorname{ord}_P C_0^\kappa(f)\ge-(\lfloor a/Q_*\rfloor+e_P-1)$;
--   2. at an unramified such place ($e_P=1$) the second term is zero: $\operatorname{ord}_P C_0^\kappa(f)\ge-\lfloor a/Q_*\rfloor$;
--   3. at every other finite place ($\operatorname{ord}_P x_0\ge0$, $P\nmid t$), an initially integral function remains integral: $\operatorname{ord}_P f\ge0\Rightarrow\operatorname{ord}_P C_0^\kappa(f)\ge0$.
--
--   Differences from the source:
--   - encoding: the tower F_h of (3.1) over k = F_{q^2}, q = p^s > 2 → any field F over any finite field k with q^2 elements (IsPrimePow q, 2 < q), with x_0 transcendental, (x_i^q + x_i)(1 + x_{i-1}^{q-1}) = x_{i-1}^q for 1 ≤ i ≤ h, and F = k(x_0, …, x_h) (IsGSTower); reason: every such F is a model of F_h; the division in φ is cleared, which excludes no instance
--   - encoding: places P and ord_P normalized to value group Z → Place k F: additive valuations F → Z ∪ {∞}, onto Z, zero on k^×; reason: places of a function field correspond one to one to their normalized valuations
--   - encoding: "the effective pole is bounded by ⌊a/Q*⌋ + e_P − 1" (a ≥ 0) → a : ℕ and ord_P C_0^κ(f) ≥ −(⌊a/Q*⌋ + e_P − 1); reason: pole orders are integers, so an integer bound loses nothing; the bound is ≥ 0 since e_P ≥ 1, so it bounds the effective pole max(0, −ord) exactly
--   - encoding: P | t; finite place; unramified → 0 < ord_P t; 0 ≤ ord_P x_0; e_P = 1 (ramIdx over k(x_0)); reason: Lean names for the same conditions
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 10, Lemma 3.2, (3.12) (PDF p. 12)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower

namespace QuasilinearAG.Encoding

/-- Lemma 3.2 (Degree-paid rounding), p. 10 (PDF 12). In the height-`h` second
Garcia–Stichtenoth tower over `k = F_{q²}` (`q > 2` a prime power), with `κ = ⌈log_q h⌉ + 1`,
`Q* = q^κ`, `t = x₀^q + x₀` and `e_P` the ramification index over `k(x₀)`:
(1) at a place `P | t`, if `a ≥ 0` bounds the pole of `f` (`ord_P f ≥ -a`), then after `κ`
extractions the effective pole is at most `⌊a/Q*⌋ + e_P - 1`, i.e. `ord_P C₀^κ(f) ≥
-(⌊a/Q*⌋ + e_P - 1)`; (2) at an unramified such place the second term is zero; (3) at every other
finite place (`ord_P x₀ ≥ 0`, `P ∤ t`) an integral function stays integral. -/
theorem lemma_3_2 {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (q h : ℕ) (hq : IsPrimePow q) (hq2 : 2 < q) (hk : Fintype.card k = q ^ 2) (hh : 1 ≤ h)
    (x : ℕ → F) (hx : IsGSTower k q h x) :
    (∀ P : Place k F, 0 < P.v (towerT q x) → ∀ (a : ℕ) (f : F),
        ((-(a : ℤ) : ℤ) : WithTop ℤ) ≤ P.v f →
        ((-(((a / q ^ kappaOf q h : ℕ) : ℤ) + (P.ramIdx (baseField x) : ℤ) - 1) : ℤ) :
            WithTop ℤ) ≤ P.v ((cartierCoeff q (towerT q x) 0)^[kappaOf q h] f)) ∧
      (∀ P : Place k F, 0 < P.v (towerT q x) → P.ramIdx (baseField x) = 1 →
        ∀ (a : ℕ) (f : F), ((-(a : ℤ) : ℤ) : WithTop ℤ) ≤ P.v f →
        ((-((a / q ^ kappaOf q h : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤
          P.v ((cartierCoeff q (towerT q x) 0)^[kappaOf q h] f)) ∧
      (∀ P : Place k F, 0 ≤ P.v (x 0) → ¬ 0 < P.v (towerT q x) → ∀ f : F, 0 ≤ P.v f →
        0 ≤ P.v ((cartierCoeff q (towerT q x) 0)^[kappaOf q h] f)) := by sorry

end QuasilinearAG.Encoding
