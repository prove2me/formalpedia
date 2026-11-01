-- Prove2me | Theorems.Thm_WildeQIT_EntManip_lemma_19_4_2
-- name    : WildeQIT.EntManip.lemma_19_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:05.429921+00:00
-- url     : https://prove2.me/theorems/cb1be61f-6cb4-409f-b723-1ef1e2db5daa
-- title:
--   Lemma 19.4.2: $\|p_X-q_X\|_1\le\varepsilon$ implies $\|\psi^p_{AB}-\psi^q_{AB}\|_1\le2\sqrt\varepsilon$
-- statement:
--   Let $p_X$ and $q_X$ be probability distributions on a finite alphabet $\mathcal X$ such that
--
--   $$
--   \|p_X-q_X\|_1\le\varepsilon .
--   $$
--
--   Then the pure states $|\psi^p\rangle_{AB}\equiv\sum_x\sqrt{p_X(x)}\,|x\rangle_A|x\rangle_B$ and $|\psi^q\rangle_{AB}\equiv\sum_x\sqrt{q_X(x)}\,|x\rangle_A|x\rangle_B$ satisfy
--
--   $$
--   \left\|\psi^p_{AB}-\psi^q_{AB}\right\|_1\le2\sqrt\varepsilon ,
--   $$
--
--   where $\psi^p_{AB}=|\psi^p\rangle\langle\psi^p|_{AB}$.
--
--   The lemma lets a classical protocol that is accurate in total variation be run coherently, on the Schmidt coefficients of a pure state, with a controlled error in trace distance.
--
--   **Formalization Note** Distributions are the published `WildeQIT.FinDist`; $\|\cdot\|_1$ is `WildeQIT.classicalTraceDist` for distributions and `WildeQIT.traceNorm` for operators. The hypothesis forces $\varepsilon\ge0$.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 19.4.2, (19.92)–(19.93), p. 547

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_classicalTraceDist
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_WildeQIT_EntManip_schmidtVec

namespace WildeQIT.EntManip

/-- **Lemma 19.4.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 547): "Let `p_X` and `q_X` be probability distributions such that `‖p_X − q_X‖₁ ≤ ε`. (19.92)
Then the quantum states `|ψ^p⟩_{AB} ≡ ∑_x √(p_X(x)) |x⟩_A|x⟩_B` and
`|ψ^q⟩_{AB} ≡ ∑_x √(q_X(x)) |x⟩_A|x⟩_B` are such that `‖ψ^p_{AB} − ψ^q_{AB}‖₁ ≤ 2√ε`." (19.93)

**Formalization Note** Distributions on a finite alphabet (published `WildeQIT.FinDist`);
`‖·‖₁` is the published `classicalTraceDist` for distributions and `traceNorm` for operators;
`ψ^p_{AB} = |ψ^p⟩⟨ψ^p|_{AB}` is the published `ObliviousRSP.pureState`. `ε ≥ 0` follows from (19.92). -/
theorem lemma_19_4_2 {X : Type} [Fintype X] [DecidableEq X] (p q : WildeQIT.FinDist X) (ε : ℝ)
    (h : WildeQIT.classicalTraceDist p.prob q.prob ≤ ε) :
    WildeQIT.traceNorm
        (ObliviousRSP.pureState (schmidtVec p.prob) - ObliviousRSP.pureState (schmidtVec q.prob))
      ≤ 2 * Real.sqrt ε := by sorry

end WildeQIT.EntManip
