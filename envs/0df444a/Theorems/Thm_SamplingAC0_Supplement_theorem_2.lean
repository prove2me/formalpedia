-- Prove2me | Theorems.Thm_SamplingAC0_Supplement_theorem_2
-- name    : SamplingAC0.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:40:56.357825+00:00
-- url     : https://prove2.me/theorems/2f46b3ea-0512-4c5c-ad6f-d0a417f1b531
-- title:
--   Theorem 2 (Reducing input length) — a $k$-local map from $r$ bits nearly preserves $F(U_m)$
-- statement:
--   Let $F:\{0,1\}^m\to Y$ be any function and
--   $$\ell:=\log_2\bigl|\mathrm{supp}(F(U_m))\bigr|,$$
--   the base-2 logarithm of the number of values $F$ takes. There are absolute constants $c_1,c_2,c_3,c_4>0$ such that for all naturals $k$ and $r$ with
--   $$c_3\le k\le r^{c_4}\qquad\text{and}\qquad \ell\le r\le 2\ell$$
--   there is a $k$-local map $G:\{0,1\}^r\to\{0,1\}^m$ with
--   $$\Delta\bigl(F(G(U_r)),\,F(U_m)\bigr)^2\;\le\; r^{-c_1k}+2^{\ell-r}\bigl(1+2^{-c_2k}\bigr)^r.$$
--   Here $U_r$, $U_m$ are uniform and $\Delta$ is statistical distance. The constants do not depend on $m$, $Y$, $F$, $k$ or $r$; the map $G$ may depend on all of them.
--
--   The theorem replaces the $m$ input bits of a sampler by $r\approx\ell$ bits through a map in which each bit reads only $k$ seed bits, so the reduction can be carried out inside AC$^0$ or NC$^0$ (Corollary 3 of the paper).
--
--   **Formalization Note** The four occurrences of $c$ in the paper's statement are four separate constants, per the paper's $c$-notation. $\ell$ is a real number, compared with $k$, $r$ and $r^{c_4}$ over the reals. Since both laws are supported on the finite range of $F$, statistical distance is the finite sum over that range, allowing the paper's arbitrary codomain $Y$.
--
--   Differences from the source:
--   - encoding: statistical distance between laws on an arbitrary set $Y$ → the defining finite sum over the range of $F$; reason: both laws are supported on this finite range, so the sum is exactly the source's statistical distance and no instance is excluded
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 2, p.3 (proof §5, pp.14–16)

import Mathlib
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_Supplement_IsLocal
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- **Theorem 2 (Reducing input length).** Riazanov–Viola, *Sampling Tools and the Power of AC0*,
STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 2, p.3 (proof §5, pp.14–16):
"Let F be a function from {0, 1}^m to Y, and define ℓ := log₂ |supp(F(U_m))|. Then there exists a
k-local map G from {0, 1}^r to {0, 1}^m such that ∆(F(G(U_r)), F(U_m))² ≤ r^{−ck} +
2^{ℓ−r}(1 + 2^{−ck})^r, for any k and r such that c ≤ k ≤ r^c and ℓ ≤ r ≤ 2ℓ."

**Formalization Note.**
* c-notation (p.2): the four occurrences of `c` are four absolute positive constants `c₁` (in
  `r^{−c₁k}`), `c₂` (in `2^{−c₂k}`), `c₃` (in `c₃ ≤ k`) and `c₄` (in `k ≤ r^{c₄}`), chosen before
  `m`, `Y`, `F`, `k` and `r`. The map `G` may depend on `F`, `k` and `r`.
* `Y` is arbitrary, as on the page. Since both distributions are supported on the finite range of
  `F`, their statistical distance is written as the finite sum over that range; classical equality
  is used only to form the range as a `Finset`.
* `supp(F(U_m))` is the range of `F` (the uniform input has full support); `ℓ` is a real number and
  `k`, `r` are compared with it, and with `r^{c₄}`, as reals.
* `F(G(U_r))` is `law (F ∘ G)` and `F(U_m)` is `law F`. -/
theorem theorem_2 : open Classical in
    ∃ c₁ c₂ c₃ c₄ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
      ∀ (m : ℕ) (Y : Type) (F : (Fin m → Bool) → Y) (k r : ℕ),
        c₃ ≤ (k : ℝ) → (k : ℝ) ≤ (r : ℝ) ^ c₄ →
        Real.logb 2 ((Finset.univ.image F).card : ℝ) ≤ (r : ℝ) →
        (r : ℝ) ≤ 2 * Real.logb 2 ((Finset.univ.image F).card : ℝ) →
        ∃ G : (Fin r → Bool) → (Fin m → Bool), IsLocal k G ∧
          ((1 / 2 : ℝ) * ∑ y ∈ Finset.univ.image F,
              |(SamplingAC0.law (F ∘ G) y).toReal - (SamplingAC0.law F y).toReal|) ^ 2 ≤
            (r : ℝ) ^ (-(c₁ * k)) +
              (2 : ℝ) ^ (Real.logb 2 ((Finset.univ.image F).card : ℝ) - r) *
                (1 + (2 : ℝ) ^ (-(c₂ * k))) ^ r := by sorry

end SamplingAC0.Supplement
