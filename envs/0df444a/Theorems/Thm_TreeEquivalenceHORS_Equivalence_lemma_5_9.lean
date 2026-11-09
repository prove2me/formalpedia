-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_9
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:32.34417+00:00
-- url     : https://prove2.me/theorems/b10e4379-77ab-40e7-a354-74b2dbbcbe90
-- title:
--   Lemma 5.9 (Binary output encoding): productive $\Sigma_0$-schemes translate effectively to productive $\Sigma_2$-schemes with $\mathrm{BT}(G^E)=E(\mathrm{BT}(G))$
-- statement:
--   There is an effective translation $G\mapsto G^E$ such that every productive HORS $G$ over $\Sigma_0$ is sent to a productive HORS $G^E$ over $\Sigma_2$ with
--   $$\operatorname{ord}(G^E)\le\max\{1,\operatorname{ord}(G)\},\qquad\mathrm{BT}(G^E)=E(\mathrm{BT}(G)),$$
--   where $E$ is the constructor encoding of Equation (26); if $G$ is safe, then $G^E$ is safe. For any productive HORS $G,H$ over $\Sigma_0$,
--   $$\mathrm{BT}(G^E)=\mathrm{BT}(H^E)\iff\mathrm{BT}(G)=\mathrm{BT}(H).$$
--
--   The input schemes are arbitrary productive schemes over $\Sigma_0$, of any order, not only compiler outputs.
--
--   Differences from the source:
--   - reading: "every productive HORS G over Σ₀" → every well-formed (`Valid`) scheme G with alphabet Σ₀ and `Prod G`; reason: a HORS in the source is always a well-formed scheme (Section 3)
--   - encoding: the construction is effective / total computable → `Computable` (Mathlib) of the induced map on natural-number codes: decode, apply the construction, encode (malformed codes go to the code of `none`); reason: the standard meaning of effectiveness of a syntax transformation under fixed encodings
--   - encoding: possibly infinite ranked trees over Σ ∪ {⊥:0} → label functions `List ℕ → Lab` giving at every address `term c`, `bot` or `absent`; reason: a ranked tree is determined by its labels at all finite addresses; infinite trees are included
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.9, printed p. 21 / PDF p. 23

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Encoding
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Syntax

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.9 (Binary output encoding)** (printed p. 21 / PDF p. 23). There is an effective
translation `G ↦ G^E` such that every productive scheme `G` over `Σ₀` is sent to a productive
scheme over `Σ₂` with `ord(G^E) ≤ max{1, ord(G)}` and `BT(G^E) = E(BT(G))`, safe whenever `G` is
safe; and for productive `G, H` over `Σ₀`, `BT(G^E) = BT(H^E) ⟺ BT(G) = BT(H)`. -/
theorem lemma_5_9 :
    ∃ f : HORS → HORS,
      Computable (fun n : ℕ => Encodable.encode ((Encodable.decode n : Option HORS).map f)) ∧
      (∀ G : HORS, G.Valid → G.alphabet = sigma0 → G.Prod →
        (f G).Valid ∧ (f G).alphabet = sigma2 ∧ (f G).Prod ∧ (f G).order ≤ max 1 G.order ∧
          (f G).BT = encAt G.BT ∧ (G.Safe → (f G).Safe)) ∧
      ∀ G H : HORS, G.Valid → H.Valid → G.alphabet = sigma0 → H.alphabet = sigma0 →
        G.Prod → H.Prod → ((f G).BT = (f H).BT ↔ G.BT = H.BT) := by sorry

end TreeEquivalenceHORS.Equivalence
