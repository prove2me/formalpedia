-- Prove2me | Theorems.Thm_QCSepTotal_fact_1
-- name    : QCSepTotal.fact_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:40:31.676759+00:00
-- url     : https://prove2.me/theorems/bf3f17e3-17ff-4c1a-9bae-9616298ce355
-- title:
--   Fact 1 — cut-and-paste: $h^2(T_{x,y},T_{x',y})+h^2(T_{x,y'},T_{x',y'})\le2h^2(T_{x,y},T_{x',y'})$
-- statement:
--   Let $\Pi$ be a randomized communication protocol, with public and private randomness, and let $T_{x,y}$ be the distribution of its communicated messages and public coins on the fixed input pair $(x,y)$. Then for all inputs $x,x'$ of Alice and $y,y'$ of Bob,
--   $$h^2\bigl(T_{x,y},T_{x',y}\bigr)+h^2\bigl(T_{x,y'},T_{x',y'}\bigr)\le 2\,h^2\bigl(T_{x,y},T_{x',y'}\bigr).$$
--
--   The paper quotes this from [5, Lemma 6.4]. In the proof of Theorem 4.1 it is applied to the auxiliary protocol in which each party privately samples its cell, which is why private coins are allowed.
--
--   Differences from the source: none.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Fact 1, p.5, eq. (4) (quoting [5, Lemma 6.4])

import Mathlib
import Definitions.Def_QCSepTotal_hellingerSq
import Definitions.Def_QCSepTotal_RandProtocol

namespace QCSepTotal

/-- **Fact 1** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.5; quoting [5, Lemma 6.4]). For a randomized
communication protocol, let `T_{x,y}` denote the distribution of its communicated messages and
public coins on the fixed input pair `(x, y)`. Then, for any `x, x′, y, y′`,
`h²(T_{x,y}, T_{x′,y}) + h²(T_{x,y′}, T_{x′,y′}) ≤ 2h²(T_{x,y}, T_{x′,y′})` (4).

**Formalization Note.** The protocol may use public and private coins; `T_{x,y}` is
`transcriptLaw`, the law of (public coins, bits sent). -/
theorem fact_1 {X Y : Type} (P : RandProtocol X Y) (x x' : X) (y y' : Y) :
    hellingerSq (P.transcriptLaw x y) (P.transcriptLaw x' y) +
        hellingerSq (P.transcriptLaw x y') (P.transcriptLaw x' y') ≤
      2 * hellingerSq (P.transcriptLaw x y) (P.transcriptLaw x' y') := by sorry

end QCSepTotal
