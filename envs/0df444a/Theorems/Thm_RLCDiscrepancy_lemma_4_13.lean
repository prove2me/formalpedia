-- Prove2me | Theorems.Thm_RLCDiscrepancy_lemma_4_13
-- name    : RLCDiscrepancy.lemma_4_13
-- status  : Disproved
-- author  : @iris
-- created : 2026-11-06T16:54:58.429198+00:00
-- url     : https://prove2.me/theorems/85f94deb-1c95-451f-9e94-57064bc47618
-- title:
--   Lemma 4.13 — smooth $F_f$ and monotone imply smooth $f$, except with probability $q^{-t^2/10}$
-- statement:
--   Let $k\le n$, let $f:\mathbb F_q^n\to\mathbb R_{\ge0}$ be normalized, let $C_0,\dots,C_k$ be a random construction sequence, let $\Gamma>0$ and let $t$ satisfy $20\log_q n\le t\le k$. Set $\Lambda=\max\{\|f\|_\infty q^{-k},\sqrt\Gamma\}$, and consider the events
--
--   1. $S_{F\text{-smooth}}(f)$: the sequence is $(F_f,\Gamma)$-smooth;
--   2. $S_{\mathrm{monotone}}(f)$: $|\delta_{C_j,f}|\le|\delta_{C_{j-1},f}|$ for every $1\le j\le k$ such that $(C_0,\dots,C_{j-1})$ is $(f,q^t\Lambda,j-1)$-smooth;
--   3. $S_{\mathrm{smooth}}(f)$: the sequence is $(f,q^t\Lambda)$-smooth.
--
--   Then
--
--   $$
--   \Pr_{C_0,\dots,C_k}\big[S_{F\text{-smooth}}(f)\wedge S_{\mathrm{monotone}}(f)\wedge\neg S_{\mathrm{smooth}}(f)\big]\le q^{-\frac1{10}t^2}.
--   $$
--
--   This is the $q^{-\Omega(t^2)}$ estimate that makes a union bound over exponentially many test functions possible.
--
--   Differences from the source:
--   - generalization: t ∈ N → t ∈ ℝ; reason: the printed proof never uses integrality of t, and the proof of Theorem 2.4 applies the lemma with t = ηn/12; integer t is a special case
--   - encoding: a random construction sequence C_0, …, C_k → uniformly random `u : Fin k → (Fin n → F)` with C_i = span of the first i vectors (`consSeq`); reason: Definition 4.1 with C_0 = {0}; 0-indexed vectors
--   - encoding: F_q and F^n_q → a finite field `F` with q = `Fintype.card F`, and `Fin n → F`; reason: every prime power is the size of a finite field; same instances
--   - encoding: Pr over a uniform random object → the counting ratio `PunctSketch.coinProb` over all outcomes; reason: the paper's law is uniform on a finite space; same values
--   - encoding: C_0, …, C_k ⊆ F^n_q with k the target dimension (§2.1: "integers k, n ∈ N with k ≤ n") → hypothesis `hkn : k ≤ n`; reason: k ≤ n is §2.1's standing assumption, inherited by every statement of §4
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.13, p.32

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_capacity
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_consSeq
import Definitions.Def_RLCDiscrepancy_IsSmooth
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_smoothLambda
import Definitions.Def_RLCDiscrepancy_IsMonotone

namespace RLCDiscrepancy

/-- **Lemma 4.13.** Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.13, p.32: "Let f : F^n_q → R≥0 be normalized, let C_0, …, C_k
be a random construction sequence, let Γ > 0, and let t ∈ N satisfy 20 log_q(n) ≤ t ≤ k. Set
Λ := max{∥f∥∞ · q^{−k}, √Γ}.
• Let S_{F-smooth}(f) denote the event that C_0, …, C_k is (F_f, Γ)-smooth.
• Let S_{monotone}(f) denote the event that |δ_{C_j,f}| ≤ |δ_{C_{j−1},f}| for all j such that
(C_0, …, C_{j−1}) is (f, q^t · Λ, j − 1)-smooth.
• Let S_{smooth}(f) denote the event that C_0, …, C_k is (f, q^t · Λ)-smooth.
Then Pr_{C_0,…,C_k}[S_{F-smooth}(f) and S_{monotone}(f) and not S_{smooth}(f)] ≤ q^{−(1/10)t²}. (9)"

**Formalization Note.** The random construction sequence is given by uniformly random
`u : Fin k → (Fin n → F)` (q^{nk} outcomes). k ≤ n is the standing assumption of §2.1. t is a
real number (the paper's t ∈ N is the special case; the proof of Theorem 2.4 applies the lemma
with t = ηn/12). q^t and q^{−t²/10} are real powers. -/
theorem lemma_4_13 {F : Type*} [Field F] [Fintype F] (n k : ℕ) (hkn : k ≤ n)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ)
    (ht : 20 * Real.logb (Fintype.card F) n ≤ t) (htk : t ≤ k) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          IsMonotone u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
      (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by sorry

end RLCDiscrepancy
