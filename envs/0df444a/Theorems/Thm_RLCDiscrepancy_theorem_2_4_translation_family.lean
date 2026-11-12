-- Prove2me | Theorems.Thm_RLCDiscrepancy_theorem_2_4_translation_family
-- name    : RLCDiscrepancy.theorem_2_4_translation_family
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:53:30.57616+00:00
-- url     : https://prove2.me/theorems/496da0bb-c7b4-4658-b590-def6304d7b42
-- title:
--   Theorem 2.4 — small deviation of a translation family
-- statement:
--   Let $\mathbb F_q$ be a finite field, $k\le n$, and let $f:\mathbb F_q^n\to\mathbb R_{\ge0}$ be normalized with capacity parameter $\beta=\frac1n\log_q\|f\|_\infty$. Let $\eta>0$ with $k=(\beta+\eta)n$ (rate $R=\beta+\eta$) and $\eta n\ge240\log_q n$, and put $\varepsilon=\eta/12$. Let $C$ be the image of a uniformly random matrix $G\in\mathbb F_q^{n\times k}$. Then, with probability at least
--
--   $$
--   1-4q^{1-\frac{\eta n}3}-\frac{q^{k-n+1}}{(q-1)^2}-q^{2n-\frac{\eta^2n^2}{1440}}
--   $$
--
--   over the choice of $C$,
--
--   $$
--   \max_{z\in\mathbb F_q^n}\ |\delta_{C,f_z}|\le q^{-\varepsilon n},
--   $$
--
--   where $f_z(x)=f(x+z)$. A random linear code slightly above the capacity threshold of $f$ thus samples every translate of $f$ with exponentially small relative error; for normalized indicators of Hamming balls this yields list-decodability above capacity (Theorem 2.9 of the paper).
--
--   Differences from the source:
--   - encoding: F_q and F^n_q → a finite field `F` with q = `Fintype.card F`, and `Fin n → F`; reason: every prime power is the size of a finite field; same instances
--   - encoding: probability over the choice of C, a random linear code of rate R → the counting ratio `PunctSketch.coinProb` over all q^{nk} matrices G, with C = `rlc G`; reason: §2.1's random generating matrix model; no full-rank conditioning in either
--   - encoding: rate R = β + η with k = Rn → `(k : ℝ) = (capacity f + η) * n` with `k ≤ n`; reason: k ≤ n is §2.1's standing assumption
--   - encoding: max_{z} |δ_{C,f_z}| ≤ q^{−εn} with ε = η/12 → ∀ z, |relDev (rlc G) (transl f z)| ≤ q^{−(η/12)n}; reason: a maximum over a finite nonempty set is bounded iff every term is
--   - encoding: δ_{C,f} = E_{x∼C}[f] − E[f] → f(C)/|C| − 1 (`relDev`); reason: Definition 2.2's own last expression
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.4, p.14

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_transl
import Definitions.Def_RLCDiscrepancy_capacity
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_rlc

namespace RLCDiscrepancy

/-- **Theorem 2.4** (small deviation of a translation family). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Theorem 2.4, p.14: "Fix a
normalized function f : F^n_q → R≥0, and let β = (1/n) · log_q ∥f∥∞. Let F = {f_z : z ∈ F^n_q} be
the family of all translations of f. Let C ⊆ F^n_q be a random linear code of rate R = β + η
(where η > 0 and k = Rn), and assume that n is large enough that ηn ≥ 240 log_q n. Let ε = η/12.
Then, with probability at least 1 − 4q^{1−ηn/3} − q^{k−n+1}/(q − 1)² − q^{2n−η²n²/1440} over the
choice of C, we have max_{z∈F^n_q} |δ_{C,f_z}| ≤ q^{−εn}."

**Formalization Note.** F_q is a finite field `F`, q = `Fintype.card F` (any prime power, for
each fixed n: q may grow with n). The random linear code is `rlc G`, the image of a uniformly
random `G : Matrix (Fin n) (Fin k) F` (no full-rank conditioning), k ≤ n by §2.1, and the
probability is the fraction of the q^{nk} matrices with the event. "k = Rn" is
`(k : ℝ) = (β + η) * n`. max_z |δ| ≤ q^{−εn} is written ∀ z, with ε = η/12 inline. All powers of
q with real exponents are `Real.rpow`. -/
theorem theorem_2_4_translation_family {F : Type*} [Field F] [Fintype F] (n k : ℕ)
    (hkn : k ≤ n) (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (η : ℝ) (hη : 0 < η)
    (hk : (k : ℝ) = (capacity f + η) * n)
    (hn : 240 * Real.logb (Fintype.card F) n ≤ η * n) :
    1 - 4 * (Fintype.card F : ℝ) ^ (1 - η * n / 3)
        - (Fintype.card F : ℝ) ^ ((k : ℝ) - n + 1) / ((Fintype.card F : ℝ) - 1) ^ 2
        - (Fintype.card F : ℝ) ^ (2 * (n : ℝ) - η ^ 2 * n ^ 2 / 1440) ≤
      PunctSketch.coinProb (fun G : Matrix (Fin n) (Fin k) F =>
        ∀ z : Fin n → F, |relDev (rlc G) (transl f z)| ≤
          (Fintype.card F : ℝ) ^ (-(η / 12) * n)) := by sorry

end RLCDiscrepancy
