-- Prove2me | Theorems.Thm_SNPTreedepth_Supplement_theorem_55
-- name    : SNPTreedepth.Supplement.theorem_55
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:57:11.842005+00:00
-- url     : https://prove2.me/theorems/31203c8c-77a2-4b3a-8e6b-aa58b0da8669
-- title:
--   Theorem 55 — a fixed ESO sentence whose model checking is NP-complete on graphs of treedepth $\le 2$
-- statement:
--   There is a fixed ESO sentence $\varphi$ such that deciding whether $G\models\varphi$ is NP-complete, even when the input graph $G$ has treedepth at most $2$.
--
--   Precisely, for one fixed $\varphi$: the language of (binary codes of) finite graphs $G$ with $G\models\varphi$ is NP-complete, and so is the language of codes of finite graphs $G$ with $\mathrm{td}(G)\le2$ and $G\models\varphi$; NP-complete means it lies in NP and every language in NP reduces to it by a polynomial-time many-one reduction.
--
--   By Theorem 1, model checking of every SNP sentence is linear-time on graphs of bounded treedepth; this theorem shows that the restriction of the first-order part to universal formulas cannot be lifted to arbitrary ESO sentences unless P = NP.
--
--   **Formalization Note** NP, polynomial-time reductions and NP-completeness are Cook's (`CookPvsNP`), over the binary alphabet, with the graph code of `instanceCode`; the sentence $\varphi$ is chosen before the language.
--
--   Differences from the source:
--   - encoding: deciding whether G ⊨ φ is NP-complete, even when td(G) ≤ 2 → CookPvsNP.NPComplete of the language {graphCode G | G a graph on Fin n, G ⊨ φ} over Bool, and CookPvsNP.NPComplete of {graphCode G | G a graph on Fin n, treedepth G ≤ 2, G ⊨ φ}; reason: Cook's classes are classes of languages over a finite alphabet; graphs on Fin n represent every finite graph up to isomorphism; the restriction to treedepth ≤ 2 is part of the language, which is the standard reading of NP-completeness on a restricted input class
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Theorem 55, p.52 (PDF p.53); ESO sentences, §6.2, p.52

import Mathlib
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SNPTreedepth_Supplement_ESOSentence
import Definitions.Def_SNPTreedepth_Supplement_instanceCode

set_option autoImplicit false

namespace SNPTreedepth.Supplement

open SNPTreedepth

/-- **Theorem 55** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.52 (PDF p.53)):
"There is a fixed ESO sentence φ such that deciding whether G ⊨ φ is NP-complete, even when the
input graph G has treedepth at most 2."

**Formalization Note** The sentence `φ` is fixed before both languages, and the statement has the
paper's two clauses for the same `φ`: deciding `G ⊨ φ` on all finite graphs (the language of the
binary codes `graphCode G` of the graphs `G` on `Fin n`, any `n`, with `G ⊨ φ`) is NP-complete, and
so is the problem restricted to inputs of treedepth at most `2` ("even when"; the language of the
codes with `td(G) ≤ 2` and `G ⊨ φ`). NP-completeness is Cook's (`CookPvsNP.NPComplete`: in NP and
every NP language reduces to it in polynomial time). `td` is the base `SNPTreedepth.treedepth`.
Graphs on `Fin n` cover every finite graph up to isomorphism, and ESO satisfaction is invariant
under isomorphism. -/
theorem theorem_55 :
    ∃ φ : ESOSentence,
      CookPvsNP.NPComplete
        {w : List Bool | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), w = graphCode G ∧ φ.Models G} ∧
      CookPvsNP.NPComplete
        {w : List Bool | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
          w = graphCode G ∧ treedepth G ≤ 2 ∧ φ.Models G} := by sorry

end SNPTreedepth.Supplement
