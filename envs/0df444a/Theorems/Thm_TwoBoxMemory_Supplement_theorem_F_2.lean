-- Prove2me | Theorems.Thm_TwoBoxMemory_Supplement_theorem_F_2
-- name    : TwoBoxMemory.Supplement.theorem_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:16:43.89141+00:00
-- url     : https://prove2.me/theorems/c4b33255-6791-4bc7-b6be-df984c915768
-- title:
--   Theorem F.2 — logarithmic covering entropy of the exceptional sets $E$ and $\mathcal E$
-- statement:
--   Let $r,s\in(0,1)$ with $\log r/\log s$ irrational, $p=1-r$, $t=1-s$, and let $E\subseteq[0,1]$, $\mathcal E\subseteq(0,\infty)$ be the exceptional sets and $c_0=\min\{u(1),v(1-)\}$.
--
--   1. Choose integers $n_B>1/t$, $n_A>1/p$, put $\ell=s^{n_B}$, $h=r^{-n_A}$, choose integers $K_A,K_B\ge1$ with $s^{K_A}<\ell/h$, $r^{K_B}<\ell/h$, and $0<\bar c\le c_0$. Then for every integer $N\ge1$, $E$ is covered by at most $m_N+1$ closed intervals of total length at most $D_N$, where
--
--   $$D_N=\frac{2}{\bar c}\Bigl[\frac{K_A(p+th)r^N}{p}+\frac{K_B(t+p/\ell)s^N}{t}\Bigr],\qquad m_N=\#\{(a,b):0\le a,b<N,\ \ell\le\beta_{ab}\le h\}.$$
--
--   2. $E$ has upper box dimension zero and Hausdorff dimension zero.
--   3. $N(E,\varepsilon)=O_{r,s}(\log(1/\varepsilon))$ as $\varepsilon\downarrow0$: there are $K>0$ and $\varepsilon_0>0$ with $N(E,\varepsilon)\le K\log(1/\varepsilon)$ for $0<\varepsilon<\varepsilon_0$, where $N(E,\varepsilon)$ is the least number of intervals of length at most $\varepsilon$ covering $E$.
--   4. $\mathcal E$ has Hausdorff dimension zero, and every compact subset of $\mathcal E$ has upper box dimension zero.
--
--   The cost ratios at which the optimal law is a single word thus form a very thin set, coverable by exponentially short intervals.
--
--   Differences from the source:
--   - encoding: closed intervals with total length at most D_N → intervals `Icc (a i) (b i)` with a i ≤ b i (degenerate allowed) and ∑ (b i − a i) ≤ D_N; reason: Lean convention; same covers
--   - reading: the constants n_A, n_B, K_A, K_B, c̄ chosen before the theorem → the cover clause holds for every admissible choice of them; reason: the paper fixes an arbitrary admissible choice, so the claim is for each such choice
--   - encoding: upper box dimension zero → `log N(S, ε) / log(1/ε) → 0` as ε ↓ 0; reason: the paper's own formulation in the proof; for a nonempty bounded set the quotient is nonnegative for ε < 1, so this is upper box dimension 0
--   - encoding: N(E, ε) = O_{r,s}(log(1/ε)) (ε ↓ 0) → ∃ K > 0, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), N(E, ε) ≤ K log(1/ε), for the fixed r, s; reason: the definition of the asymptotic bound
--   - reading: every compact part of 𝓔 → every compact subset K ⊆ 𝓔; reason: 𝓔 is relatively closed in (0, ∞), so its compact parts 𝓔 ∩ [a, b] are compact subsets, and every compact subset lies in one of them
--   - encoding: Hausdorff dimension → Mathlib `dimH` (value in `ℝ≥0∞`) equal to 0; reason: Lean convention; same notion
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem F.2 and (F.1), p.49 (PDF 51); E and 𝓔, p.48 (PDF 50); c₀ of Lemma E.2, p.43 (PDF 45)

import Mathlib
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Supplement_CostDomain
import Definitions.Def_TwoBoxMemory_Supplement_Cover

namespace TwoBoxMemory.Supplement

open TwoBoxMemory

/-- Theorem F.2 (Logarithmic covering entropy). Let `r, s ∈ (0, 1)` with `log r / log s`
irrational, `p = 1 − r`, `t = 1 − s`.
1. For every admissible choice of the constants of (F.1) — integers `n_B > 1/t`, `n_A > 1/p`,
   `ℓ = s^{n_B}`, `h = r^{−n_A}`, integers `K_A, K_B ≥ 1` with `s^{K_A} < ℓ/h`, `r^{K_B} < ℓ/h`,
   and `0 < c̄ ≤ c₀` — and every integer `N ≥ 1`, the set `E ⊆ [0, 1]` is covered by at most
   `m_N + 1` closed intervals with total length at most `D_N`.
2. `E` has upper box dimension zero and Hausdorff dimension zero.
3. `N(E, ε) = O_{r,s}(log(1/ε))` as `ε ↓ 0`: there are `K > 0`, `ε₀ > 0` (depending on `r, s`
   only) with `N(E, ε) ≤ K log(1/ε)` for `0 < ε < ε₀`.
4. The exceptional cost set `𝓔 ⊆ (0, ∞)` has Hausdorff dimension zero, and every compact subset of
   `𝓔` has upper box dimension zero.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem F.2 and (F.1), p.49 (PDF 51); `E`, `𝓔` of p.48 (PDF 50); `c₀` of Lemma E.2, p.43 (PDF 45).

**Formalization Note.** Closed intervals are `Set.Icc (a k) (b k)` with `a k ≤ b k` (degenerate
intervals allowed); their total length is `∑ (b k − a k)`. Hausdorff dimension is Mathlib's
`dimH` (in `ℝ≥0∞`). Upper box dimension zero is `UpperBoxDimZero` (`log N(S, ε)/log(1/ε) → 0`).
No box dimension is asserted for the unbounded set `𝓔` itself. -/
theorem theorem_F_2 (r s : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hirr : Irrational (Real.log r / Real.log s)) :
    (∀ (nA nB KA KB : ℕ) (cbar : ℝ),
      1 / (1 - s) < nB → 1 / (1 - r) < nA → 1 ≤ KA → 1 ≤ KB →
      s ^ KA < coverL s nB / coverH r nA → r ^ KB < coverL s nB / coverH r nA →
      0 < cbar → cbar ≤ cZero r s →
      ∀ N : ℕ, 1 ≤ N →
        ∃ (k : ℕ) (a b : Fin k → ℝ), k ≤ coverM r s nA nB N + 1 ∧ (∀ i, a i ≤ b i) ∧
          Eset r s ⊆ ⋃ i, Set.Icc (a i) (b i) ∧
          ∑ i, (b i - a i) ≤ coverD r s nA nB KA KB cbar N) ∧
    UpperBoxDimZero (Eset r s) ∧ dimH (Eset r s) = 0 ∧
    (∃ K : ℝ, 0 < K ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (coveringNumber (Eset r s) ε : ℝ) ≤ K * Real.log (1 / ε)) ∧
    dimH (EcalSet r s) = 0 ∧
    (∀ K : Set ℝ, K ⊆ EcalSet r s → IsCompact K → UpperBoxDimZero K) := by sorry

end TwoBoxMemory.Supplement
