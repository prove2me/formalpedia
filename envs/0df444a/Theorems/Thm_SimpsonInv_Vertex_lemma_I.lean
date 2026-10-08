-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_lemma_I
-- name    : SimpsonInv.Vertex.lemma_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:42.208767+00:00
-- url     : https://prove2.me/theorems/4a9587f5-0858-494e-8eca-1041db74caf6
-- title:
--   LEMMA I, p. 872 — no interior point of D minimizes f
-- statement:
--   Let $n = m + 1$ with $m \ge 1$ variables $S_1, \dots, S_{n-1}$, let $c, S_0, S_n, T_1, \dots, T_n$ be real constants and $r_1, \dots, r_n > 0$. Let $D \subseteq \mathbb R^{n-1}$ be the domain ($S_i \ge 0$, $S_{i-1} - S_i + T_i \ge 0$) and
--   $$
--   f(S_1, \dots, S_{n-1}) = c + \sum_{i=1}^{n} r_i \sqrt{S_{i-1} - S_i + T_i}.
--   $$
--   Then no point $v$ of the interior of $D$ is a minimizer of $f$ over $D$: for every interior point $v$ there is $S \in D$ with $f(S) < f(v)$.
--
--   Lemma I is the base step of the Appendix's induction: the minimum lies on the boundary of $D$.
--
--   **Formalization Note** $r_i > 0$ comes from equation (8) ("$c$ and $r_i$ are positive constants"). The hypothesis $m \ge 1$ is added: with no variables a nonempty $D$ is all of $\mathbb R^0$, equal to its interior, and the lemma fails; the paper tacitly has at least one variable. Interior is taken in `Fin m → ℝ` with the Euclidean topology. Lean index $j$ is the paper's $S_{j+1}$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 872, LEMMA I

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem lemma_I {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (hm : 1 ≤ m)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i) :
    ∀ v ∈ interior (dom (m := m) T S0 Sn),
      ¬ IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v := by sorry

end SimpsonInv.Vertex
