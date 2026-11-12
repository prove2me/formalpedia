-- Prove2me | Theorems.Thm_RLCDiscrepancy_lemma_4_13_of_ten_le
-- name    : RLCDiscrepancy.lemma_4_13_of_ten_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:50:09.78251+00:00
-- url     : https://prove2.me/theorems/f17bfa7e-b149-4cd2-83c4-7324c9a37bbe
-- title:
--   Lemma 4.13 — a bad deviation of the self-convolution-smooth, monotone sequence has probability at most q^(−t²/10), for t ≥ 10
-- statement:
--   Let $f : \mathbb F_q^n \to \mathbb R_{\ge 0}$ be normalized, $k \le n$, $\Gamma > 0$, and let $t$ be a real number with $20\log_q n \le t \le k$ and $t \ge 10$. Put $\Lambda = \max\{\|f\|_\infty q^{-k}, \sqrt{\Gamma}\}$. For uniformly random vectors $u_1,\dots,u_k \in \mathbb F_q^n$, with $C_i = \mathrm{span}(u_1,\dots,u_i)$ and $\delta_{C,g}$ the relative deviation, the probability that all of the following hold is at most $q^{-t^2/10}$:
--
--   - the sequence $C_0,\dots,C_k$ is $(F_f,\Gamma)$-smooth, that is $|\delta_{C_i,F_f}| \le q^{k-i}\Gamma$ for all $0 \le i \le k$;
--   - $|\delta_{C_j,f}| \le |\delta_{C_{j-1},f}|$ for every $j$ such that $C_0,\dots,C_{j-1}$ is $(f, q^t\Lambda, j-1)$-smooth;
--   - the sequence is not $(f, q^t\Lambda)$-smooth, that is $|\delta_{C_i,f}| > q^{k-i}\,q^t\Lambda$ for some $0 \le i \le k$.
--
--   This is Lemma 4.13 of Doron, Leonov, Mosheiff, Navas, Resch and Ribeiro, *Discrepancy for Random Linear Codes* (STOC 2027 submission 497, p. 32), where $t$ is a natural number. The statement `RLCDiscrepancy.lemma_4_13`, which takes $t$ real with no lower bound, is false for $t < 1/2$ (see its disproof); the hypothesis $t \ge 10$ here is what the printed proof supports and what the application in Lemma 4.14 and Theorem 2.4 needs, where the claim is non-trivial only for $t > 10$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, "Discrepancy for Random Linear Codes", arXiv:2606.24471, Lemma 4.13, p. 32 (STOC 2027 submission 497, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/497.pdf), with t >= 10.

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_consSeq
import Definitions.Def_RLCDiscrepancy_IsSmooth
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_smoothLambda
import Definitions.Def_RLCDiscrepancy_IsMonotone

namespace RLCDiscrepancy

theorem lemma_4_13_of_ten_le {F : Type*} [Field F] [Fintype F] (n k : ℕ) (hkn : k ≤ n)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ)
    (ht : 20 * Real.logb (Fintype.card F) n ≤ t) (htk : t ≤ k) (ht10 : 10 ≤ t) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          IsMonotone u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
      (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by sorry

end RLCDiscrepancy
