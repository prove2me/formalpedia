-- Prove2me | Theorems.Thm_TriFormQ_lemma_1
-- name    : TriFormQ.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:12.631743+00:00
-- url     : https://prove2.me/theorems/261e749b-3df7-41a5-ac06-0bc06cca3f52
-- title:
--   Lemma 1 (generalized Bernstein–Vazirani): one query recovers $a$ from $x\mapsto a^\top x$ exactly
-- statement:
--   Let $\mathbb F_q$ be a finite field and $n\ge 0$. There is a one-query quantum algorithm with the following property: for every unknown $a\in\mathbb F_q^n$, given the evaluation oracle of the linear function
--
--   $$g(x)=a^\top x,\qquad |x\rangle|b\rangle\mapsto|x\rangle|b+a^\top x\rangle,$$
--
--   the algorithm outputs $a$ with probability exactly $1$.
--
--   This is the basic query primitive of the paper: fixing two of the three arguments of a trilinear form leaves a linear function, which is learned with one query.
--
--   Differences from the source:
--   - encoding: an exact quantum algorithm that recovers $a$ using one query → a one-query `QueryAlg` with a workspace and a classical output map, chosen before $a$, whose output equals $a$ with probability $1$; reason: platform query model
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 1 (Generalized Bernstein–Vazirani), p.11 (PDF p.14)

import Definitions.Def_TriFormQ_TriForm
import Definitions.Def_QAlgorithms_Defs_Query
open Matrix

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 1 (Generalized
Bernstein–Vazirani), p.11 (PDF p.14): "Let a ∈ 𝔽_q^n be unknown, and suppose we have g(x) = aᵀx
for x ∈ 𝔽_q^n. There is an exact quantum algorithm that recovers a using one query to the
evaluation oracle."

**Formalization Note.** The algorithm is a one-query `QAlgorithms.QueryAlg` with query register
`𝔽_q^n × 𝔽_q`, some workspace `Fin w`, the standard oracle `|x, b⟩ ↦ |x, b + aᵀx⟩`, and a
classical post-processing `out` of the full measurement outcome. It is chosen before `a`, and
"exact" is output probability exactly 1 for every `a`. -/
theorem lemma_1 {F : Type} [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    ∃ (w : ℕ) (A : QAlgorithms.QueryAlg (Vec F n) F (Fin w) 1)
      (out : (Vec F n × F) × Fin w → Vec F n),
      ∀ a : Vec F n, A.outputProb (QAlgorithms.xorOracle fun x : Vec F n => a ⬝ᵥ x) out a = 1 := by sorry

end TriFormQ
