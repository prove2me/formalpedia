-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_5
-- name    : QuantumXoP.Security.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:32.886253+00:00
-- url     : https://prove2.me/theorems/8dc967df-1210-4fd0-8302-20094b510e42
-- title:
--   Lemma 6.5 — collision structure of the small-range distribution
-- statement:
--   Let $N\ge4$ and $R\ge N^2$. For $h=g\circ f\leftarrow S_R$ let $C_f=|\{\{x,x'\}:x\ne x',\ f(x)=f(x')\}|$. Then
--   $$\Pr[C_f=1]\ge\frac{N^2}{8R},\qquad\Pr[C_f\ge2]\le\frac{N^4}{8R^2}.$$
--   Moreover, conditioned on $C_f=0$ the law of $h$ is the uniform distribution $D_F$, and conditioned on $C_f=1$ it is $D_{PC}$.
--
--   It splits $S_R$ into $D_F$, $D_{PC}$ and a remainder, which turns Theorem 6.4 into Lemma 6.6.
--
--   **Formalization Note** "The law of $h$ conditioned on $C_f=k$ is $D$" is written $\Pr[C_f=k,\ h=h_0]=\Pr[C_f=k]\,D(h_0)$ for every $h_0$.
--
--   Differences from the source:
--   - encoding: S_R samples g uniformly on the image I of f (Definition 6.3) → g is sampled uniformly on all of [R] = Fin R; reason: the law of h = g ∘ f is the same, since only the values of g on I are used
--   - encoding: the conditional law of h given C_f = k equals D → Pr[C_f = k ∧ h = h₀] = Pr[C_f = k] · D(h₀) for every h₀; reason: equivalent whenever Pr[C_f = k] > 0, which holds for k = 0 and k = 1 when R ≥ N² ≥ 16
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 27 (PDF p. 29), Lemma 6.5

import Mathlib
import Definitions.Def_QuantumXoP_Security_Planted

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 6.5 (p. 27): for `N ≥ 4` and `R ≥ N²`, with `h = g ∘ f ← S_R` and `C_f` the number of
colliding pairs of `f`: `Pr[C_f = 1] ≥ N²/(8R)`, `Pr[C_f ≥ 2] ≤ N⁴/(8R²)`; conditioned on
`C_f = 0` the law of `h` is `D_F`, and conditioned on `C_f = 1` it is `D_PC`. -/
theorem lemma_6_5 (n R : ℕ) [NeZero R] (hN : 4 ≤ 2 ^ n) (hR : (2 ^ n) ^ 2 ≤ R) :
    bigN n ^ 2 / (8 * R) ≤ probOf (srJoint n R) (fun p => collCount p.1 = 1) ∧
    probOf (srJoint n R) (fun p => 2 ≤ collCount p.1) ≤ bigN n ^ 4 / (8 * (R : ℝ) ^ 2) ∧
    (∀ h : Fn n, probOf (srJoint n R) (fun p => collCount p.1 = 0 ∧ p.2 ∘ p.1 = h) =
      probOf (srJoint n R) (fun p => collCount p.1 = 0) * ((uniformF n) h).toReal) ∧
    (∀ h : Fn n, probOf (srJoint n R) (fun p => collCount p.1 = 1 ∧ p.2 ∘ p.1 = h) =
      probOf (srJoint n R) (fun p => collCount p.1 = 1) *
        ((pcLaw n (le_trans (by norm_num) hN)) h).toReal) := by sorry

end QuantumXoP.Security
