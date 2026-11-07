-- Prove2me | Theorems.Thm_RLCDiscrepancy_lemma_4_14
-- name    : RLCDiscrepancy.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:07.372207+00:00
-- url     : https://prove2.me/theorems/b08eae20-ccf9-40a0-ad82-d5d23015a9dd
-- title:
--   Lemma 4.14 — smooth $F_f$ implies smooth $f$, except with probability $q^n q^{-t^2/10}$
-- statement:
--   In the setting of Lemma 4.13 ($k\le n$, $f$ normalized, $\Gamma>0$, $20\log_q n\le t\le k$, $\Lambda=\max\{\|f\|_\infty q^{-k},\sqrt\Gamma\}$, $C_0,\dots,C_k$ a random construction sequence),
--
--   $$
--   \Pr_{C_0,\dots,C_k}\big[S_{F\text{-smooth}}(f)\wedge\neg S_{\mathrm{smooth}}(f)\big]\le q^n\cdot q^{-0.1t^2},
--   $$
--
--   where $S_{F\text{-smooth}}(f)$ is $(F_f,\Gamma)$-smoothness and $S_{\mathrm{smooth}}(f)$ is $(f,q^t\Lambda)$-smoothness. The monotonicity hypothesis of Lemma 4.13 is removed at the price of the factor $q^n$.
--
--   Differences from the source:
--   - generalization: t ∈ N → t ∈ ℝ; reason: the printed proof never uses integrality of t, and the proof of Theorem 2.4 applies the lemma with t = ηn/12; integer t is a special case
--   - encoding: a random construction sequence C_0, …, C_k → uniformly random `u : Fin k → (Fin n → F)` with C_i = span of the first i vectors (`consSeq`); reason: Definition 4.1 with C_0 = {0}; 0-indexed vectors
--   - encoding: F_q and F^n_q → a finite field `F` with q = `Fintype.card F`, and `Fin n → F`; reason: every prime power is the size of a finite field; same instances
--   - encoding: Pr over a uniform random object → the counting ratio `PunctSketch.coinProb` over all outcomes; reason: the paper's law is uniform on a finite space; same values
--   - encoding: C_0, …, C_k ⊆ F^n_q with k the target dimension (§2.1: "integers k, n ∈ N with k ≤ n") → hypothesis `hkn : k ≤ n`; reason: k ≤ n is §2.1's standing assumption, inherited by every statement of §4
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.14, p.36

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

/-- **Lemma 4.14** (the monotone hypothesis removed). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.14, p.36: "In the setting of
Lemma 4.13, Pr_{C_0,…,C_k}[S_{F-smooth}(f) and not S_{smooth}(f)] ≤ q^n · q^{−0.1t²}."

**Formalization Note.** The setting of Lemma 4.13: normalized f, Γ > 0, t with
20 log_q n ≤ t ≤ k (t real, containing the printed t ∈ N), k ≤ n, Λ = max{∥f∥∞ q^{−k}, √Γ},
uniformly random `u : Fin k → (Fin n → F)`. -/
theorem lemma_4_14 {F : Type*} [Field F] [Fintype F] (n k : ℕ) (hkn : k ≤ n)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ)
    (ht : 20 * Real.logb (Fintype.card F) n ≤ t) (htk : t ≤ k) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
      (Fintype.card F : ℝ) ^ n * (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by sorry

end RLCDiscrepancy
