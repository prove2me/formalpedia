-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_4_2
-- name    : SoftmaxAttnFD.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:24.792865+00:00
-- url     : https://prove2.me/theorems/ee2f9112-216a-42ed-85c9-7db287a594b7
-- title:
--   Lemma 4.2, p.15 (= Lemma 5.7, p.22) — $\mathrm{KP}_2$ deterministically in $\tilde O(m+n)$
-- statement:
--   Let $U,W\ge1$ be integer bounds on the absolute values of the geometric coordinates and input weights in $\mathbb Q$, and let $b$ bound their encoding lengths and that of the tolerance $\eta\in\mathbb Q\cap(0,1]$. There are a coin-free program and constants $C>0$, $K$ such that each of $Tw_{\rm in}$ and $T^\top z_{\rm in}$ is computed to coordinatewise additive error at most $\eta$ at bit cost at most
--   $$C\,(m+n)\,\bigl(b+\log_2(m+n)+\log_2U+\log_2W\bigr)^K.$$
--   This is the base case of the induction on the dimension.
--
--   Differences from the source:
--   - encoding: "computed deterministically … in Õ(m + n) time" → one coin-free program of the logarithmic-cost RAM on the KP layout; bit cost C(m+n)(b + log₂(m+n) + log₂U + log₂W)^K; m, n ≥ 1; reason: the page names no machine (Machine); log(1/η) is covered by b
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 4.2, p.15; Lemma 5.7, p.22

import Definitions.Def_SoftmaxAttnFD_KernelProducts

namespace SoftmaxAttnFD

/-- **Lemma 4.2** (arXiv:2611.06055, sha256 a60f7609…, p.15), stated again as **Lemma 5.7** (p.22).
Each of `T w_in` and `T^⊤ z_in` can be computed deterministically to coordinatewise additive error at
most `η` in `Õ(m + n)` time. `KP_2` can be solved deterministically in `Õ(m + n)` time.

**Formalization Note** One coin-free program reads the mode, on the layouts of `KPSolvable`. -/
theorem lemma_4_2 :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (m n : ℕ) (η : RatEnc) (q : Fin m → Fin 2 → RatEnc) (k : Fin n → Fin 2 → RatEnc)
        (U W b : ℕ), KPBounds η q k U W b →
        (∀ w : Fin n → RatEnc, VecBounded w W b →
          DeterministicWithin P (memOf (kpForwardInput η q k w)) (kpForwardGood η q k w)
            (C * ((m : ℝ) + n) * lamKP b m n U W ^ K)) ∧
        (∀ z : Fin m → RatEnc, VecBounded z W b →
          DeterministicWithin P (memOf (kpTransposeInput η q k z)) (kpTransposeGood η q k z)
            (C * ((m : ℝ) + n) * lamKP b m n U W ^ K)) := by sorry

end SoftmaxAttnFD
