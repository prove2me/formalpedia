-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_B_1
-- name    : TensorBeyond.Main.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:59.228415+00:00
-- url     : https://prove2.me/theorems/6bc6f9a9-fbb4-461d-800c-ff294f3bfbc8
-- title:
--   Lemma B.1 — $\{x_u^2=1\}\vdash_8 |R_8(x)-s_8(x)|\le C\log^9n/n$
-- statement:
--   Let $n\ge16$, $n\le m\le n^3$, $v_1,\dots,v_m$ i.i.d. uniform in $\{\pm1\}^n$, $R_8(x)=\sum_i\langle v_i,x\rangle^8$ with $\langle x,y\rangle=\frac1nx^\top y$, and $s_8$ the $8$-legged spider polynomial. There is an absolute constant $C>0$ such that, for every $c>0$ and all $n$ beyond some $N_0(c)$, with probability at least $1-(\log n)^{-c}$,
--   $$\{x_u^2=1:u\in[n]\}\ \vdash_8\ -\frac{C\log^9n}{n}\ \le\ R_8(x)-s_8(x)\ \le\ \frac{C\log^9n}{n},$$
--   and in particular every pseudo-expectation of degree at least $8$ satisfying the Boolean constraints obeys $|\tilde{\mathbb E}[R_8]-\tilde{\mathbb E}[s_8]|\le C\log^9n/n$, which tends to $0$.
--
--   This transfers the lower bound on the spider polynomial $s_8$ to the eighth moment $R_8$ in the proof of Lemma 6.3.
--
--   Differences from the source:
--   - reading: "with high probability" → for every c there is N₀ with probability ≥ 1 − (log n)^{−c}, C chosen before c; reason: the paper's convention 1 − õ(1) (Theorem 6.1) with "for every c", the stronger reading
--   - encoding: the intersection polynomial q_{8,int}, defined in the statement but not used in (B.1) → not formalized; reason: it does not occur in any conclusion
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), pp. 71–72 (PDF 73–74), Lemma B.1, (B.1)

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma B.1: there is an absolute constant `K > 0` such that for every `c > 0` there is `N₀`
with: for all `n ≥ 16`, `n ≥ N₀`, `n ≤ m ≤ n³`, with probability at least `1 − (log n)^{−c}`,
`{x_u² = 1} ⊢_8 −K log⁹n/n ≤ R_8(x) − s_8(x) ≤ K log⁹n/n` (both derivations), and every
pseudo-expectation of degree at least `8` satisfying the Boolean constraints has
`|Ẽ[R_8] − Ẽ[s_8]| ≤ K log⁹n/n`; moreover `K log⁹n/n → 0`. -/
theorem lemma_B_1 :
    ∃ K : ℝ, 0 < K ∧
      Filter.Tendsto (fun n : ℕ => K * Real.log (n : ℝ) ^ 9 / (n : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ c : ℝ, 0 < c → ∃ N₀ : ℕ, ∀ n m : ℕ, 16 ≤ n → N₀ ≤ n → n ≤ m → m ≤ n ^ 3 →
        1 - Real.log (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
          SoSProves 8 [] (R v 8 - spider v 8 +
            MvPolynomial.C (K * Real.log (n : ℝ) ^ 9 / (n : ℝ))) ∧
          SoSProves 8 [] (MvPolynomial.C (K * Real.log (n : ℝ) ^ 9 / (n : ℝ)) -
            (R v 8 - spider v 8)) ∧
          ∀ (D : ℝ), 8 ≤ D → ∀ E : Poly n →ₗ[ℝ] ℝ, IsPseudoExp D [] E →
            |E (R v 8) - E (spider v 8)| ≤ K * Real.log (n : ℝ) ^ 9 / (n : ℝ)) := by sorry

end TensorBeyond.Main
