-- Prove2me | Theorems.Thm_TwoBoxMemory_eq_B10_B11_walk
-- name    : TwoBoxMemory.eq_B10_B11_walk
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:21.475198+00:00
-- url     : https://prove2.me/theorems/baf0e8e7-a9e9-4d9f-8ca0-606d205329bc
-- title:
--   (B.10)–(B.11) — the log-index walk, survival decay, non-periodicity and runs
-- statement:
--   Throughout, $(r,s,\beta,D)$ is a **non-tie positive saddle with irrational logarithmic failure ratio**: $r,s\in(0,1)$ are the failure probabilities at locations $A$ and $B$ ($p=1-r$, $t=1-s$), $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\neq s^j$ for all $i,j\ge0$, $u=1/p-H_B>0$, $v=1/t-H_A>0$ and $D>0$; the cost of command $A$ is the saddle cost $C=Dv/u$, and $W$ is the greedy word. Along $W$ let $z_h=\log\beta-AN_A(h)+BN_B(h)$, $A=-\log r$, $B=-\log s$, $S=A+B$, $\alpha=B/S$. Then:
--
--   1. $|z_h|\le Z_0$ for all $h$;
--   2. $N_A(h)=\alpha h+(\log\beta-z_h)/S$;
--   3. $r^{N_A(h)}\le K_0\tau^h$ and $s^{N_B(h)}\le K_0\tau^h$;
--   4. $N_A(h)/h\to\alpha$ and $\alpha$ is irrational;
--   5. $W$ is not eventually periodic;
--   6. for $i<j$ the common-prefix set $\{n: W_{i+k}=W_{j+k}\ (k<n)\}$ is bounded, so every $\ell(i,j)$ is finite;
--   7. every run of $A$'s has at most $Z_0/A+1$ commands, every run of $B$'s at most $Z_0/B+1$, and every constant-symbol run, the initial one included, at most $R=\lceil Z_0/\min(A,B)\rceil+2$.
--
--   These are the dynamical facts behind the deterministic upper bound and the finiteness of the repetition profile.
--
--   Differences from the source:
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), (B.10)–(B.11), p.23 (PDF 25); (B.5), p.22 (PDF 24); §6, p.9 (PDF 11)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- (B.10)–(B.11): the log-index walk, decay of the survival factors, non-periodicity and runs.
At a non-tie positive saddle, along the greedy word `W` with `z_h = log β − A N_A(h) + B N_B(h)`:
1. `|z_h| ≤ Z₀` for all `h`;
2. `N_A(h) = α h + (log β − z_h)/S`;
3. `r^{N_A(h)} ≤ K₀ τ^h` and `s^{N_B(h)} ≤ K₀ τ^h`;
4. `N_A(h)/h → α`, and `α` is irrational;
5. `W` is not eventually periodic;
6. every common-prefix set `{n : W_{i+k} = W_{j+k} (k < n)}`, `i < j`, is bounded (the
   "All these numbers are finite" of (B.5));
7. every `A` run has at most `Z₀/A + 1` commands, every `B` run at most `Z₀/B + 1`, and every
   constant-symbol run (the initial one included) at most `R = ⌈Z₀ / min(A, B)⌉ + 2`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
(B.10)–(B.11), p.23 (PDF 25); (B.5), p.22 (PDF 24); §6, p.9 (PDF 11).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem eq_B10_B11_walk (r s β D : ℝ) (hS : IsSaddle r s β D) :
    (∀ h : ℕ, |logWalk r s β h| ≤ Z0 r s β) ∧
    (∀ h : ℕ, ((greedyCounts r s β h).1 : ℝ) =
      alpha r s * h + (Real.log β - logWalk r s β h) / logS r s) ∧
    (∀ h : ℕ, r ^ (greedyCounts r s β h).1 ≤ K0 r s β * tau r s ^ h ∧
      s ^ (greedyCounts r s β h).2 ≤ K0 r s β * tau r s ^ h) ∧
    Filter.Tendsto (fun h : ℕ => ((greedyCounts r s β h).1 : ℝ) / h) Filter.atTop
      (nhds (alpha r s)) ∧
    Irrational (alpha r s) ∧
    (¬ ∃ q > 0, ∃ h₀ : ℕ, ∀ h ≥ h₀, greedyWord r s β (h + q) = greedyWord r s β h) ∧
    (∀ i j : ℕ, i < j →
      BddAbove {n : ℕ | ∀ k < n, greedyWord r s β (i + k) = greedyWord r s β (j + k)}) ∧
    (∀ h n : ℕ, (∀ k < n, greedyWord r s β (h + k) = 0) → (n : ℝ) ≤ Z0 r s β / logA r + 1) ∧
    (∀ h n : ℕ, (∀ k < n, greedyWord r s β (h + k) = 1) → (n : ℝ) ≤ Z0 r s β / logB s + 1) ∧
    (∀ h n : ℕ, (∀ k < n, greedyWord r s β (h + k) = greedyWord r s β h) →
      n ≤ runBound r s β) := by sorry

end TwoBoxMemory
