-- Prove2me | Theorems.Thm_SoftmaxAttnFD_Supplement_theorem_4_1
-- name    : SoftmaxAttnFD.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:43:11.551578+00:00
-- url     : https://prove2.me/theorems/de300da1-b1ec-4b52-a8ac-3f7ae6806f07
-- title:
--   Theorem 4.1, p.14 — planar attention ($d=2$, any fixed $r$) deterministically in $\tilde O(m+n)$
-- statement:
--   Fix $d=2$ and an integer $r\ge1$ of value channels. There are a coin-free program of the logarithmic-cost RAM and constants $C>0$, $K$ such that for all $m,n\ge1$, $p\ge0$ and all rational $Q\in\mathbb Q^{m\times2}$, $K_e\in\mathbb Q^{n\times2}$, $V\in\mathbb Q^{n\times r}$ with entries of magnitude at most $B\ge1$ and encoding length at most $b$, on every run the program halts with an output $\hat O$ satisfying
--
--   $$\|\hat O-\mathrm{Att}(Q,K_e,V)\|_{\max}\le2^{-p},$$
--
--   within bit cost
--
--   $$C\,(m+n)\,\bigl(b+\log_2(m+n)+\log_2B+p\bigr)^K .$$
--
--   That is, for $d=2$ approximate attention (Definition 2.1) is computed deterministically in $\tilde O(N)$ time, $N=m+n$. This is the base case of the paper's dimension induction and is deterministic, unlike the Las Vegas goal at $d=2$.
--
--   **Formalization Note** The program, $C$ and $K$ are chosen after $r$ and before the instance. The soft-O suppresses factors polynomial in $b$, $\log(m+n)$, $\log B$ and $\log(1/\varepsilon)=p$ (§2), all dominated by the power of the base, which is at least $1$.
--
--   Differences from the source:
--   - encoding: "computed deterministically in Õ(N) time" → one coin-free program of the logarithmic-cost RAM that on every tape halts with a correct output within bit cost C(m+n)(b + log₂(m+n) + log₂B + p)^K, program, C, K chosen after r; 1 ≤ r, 1 ≤ m, n (positive numbers of value channels, queries and keys, as in the published goal); reason: the page names no machine (base Machine); soft-O as defined in §2, as in the published goal
--   - encoding: rational input and output matrices → encoded triples at fixed addresses (base Attention layout); B, b bounds under ∀ and not inputs; reason: covers every encoding the page allows, as in the published goal
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Theorem 4.1, p.14 (PDF p.17); proof in §4.5, p.18; Definition 2.1, p.10

import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_SoftmaxAttnFD_Attention

namespace SoftmaxAttnFD

namespace Supplement

/-- **Theorem 4.1** (Planar attention; Huang, Chen, Softmax Attention with Any Temperature in Fixed
Dimension, arXiv:2611.06055, sha256 a60f7609…, p.14; proof in §4.5, p.18). For `d = 2` and any fixed
number `r` of value channels, approximate attention as defined in Definition 2.1 can be computed
deterministically in `Õ(N)` time, `N = m + n`.

**Formalization Note** One coin-free program of the logarithmic-cost RAM (`DeterministicWithin`: no
`coin` instruction, and on every tape the run halts within the bound with a correct output), chosen
with `C`, `K` after `r` and before the instance. Soft-O suppresses factors polynomial in `b`,
`log(m + n)`, `log B` and `log(1/ε) = p` (§2, pp.9–10); the base of the power is at least 1, so it
dominates every such polynomial. `B` and `b` are bounds, not inputs. -/
theorem theorem_4_1 (r : ℕ) (hr : 1 ≤ r) :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (m n p : ℕ), 1 ≤ m → 1 ≤ n →
        ∀ (Q : Fin m → Fin 2 → RatEnc) (Kₑ : Fin n → Fin 2 → RatEnc) (V : Fin n → Fin r → RatEnc)
          (B : ℝ) (b : ℕ), 1 ≤ B → MatBounded Q B b → MatBounded Kₑ B b → MatBounded V B b →
          DeterministicWithin P (attnMem p Q Kₑ V) (attnGood p Q Kₑ V)
            (C * ((m : ℝ) + n) * ((b : ℝ) + Real.logb 2 ((m : ℝ) + n) + Real.logb 2 B + p) ^ K) := by sorry

end Supplement

end SoftmaxAttnFD
