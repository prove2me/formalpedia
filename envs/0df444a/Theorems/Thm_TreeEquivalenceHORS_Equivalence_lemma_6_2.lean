-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_6_2
-- name    : TreeEquivalenceHORS.Equivalence.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:13.142214+00:00
-- url     : https://prove2.me/theorems/4bdf0902-302a-40f0-9ee5-ae3fc3e03fd1
-- title:
--   Lemma 6.2 (Exact prefixes): the reader returns the exact label, $\bot$ or absence, and exact prefixes are total computable
-- statement:
--   For every well-formed scheme $G$, closed ground term $t$ and finite address $w$, the reader $\mathrm{read}_G(t,w)$ of Section 6.4 terminates and returns exactly the label, the bottom node, or the absence at address $w$ in $\mathrm{BT}_G(t)$. Consequently the exact prefixes $\mathrm{Pref}(G,t,d)$ of every specified finite depth $d$ are total computable: some total computable function maps the codes of $G$, $t$ and $d$ to the code of $\mathrm{Pref}(G,t,d)$ whenever $G$ is well formed and $t$ closed ground.
--
--   No productivity, safety or order bound is assumed; empty terminal alphabets are included.
--
--   Differences from the source:
--   - encoding: the reader returns a label, ⊥ or †, and terminates → `read` is a Mathlib partial computation (`Part Lab`); "terminates and returns ℓ" is `read G t w = Part.some ℓ`; reason: termination of the budget search is a conclusion, so the reader is defined as a partial function
--   - encoding: exact prefixes of any specified finite depth are total computable → there is a `Computable f : ℕ × ℕ × ℕ → ℕ` with `f (encode G, encode t, d) = encode (Pref G t d)` for every valid G and closed ground t; reason: computability of the prefix map on codes under the fixed encodings
--   - encoding: standard computable injective encodings of finite syntax by natural numbers, with total computable decoders that return syntax or reject → the derived `Encodable` instances of `Ty`, `Tm`, `HORS`, `Instr` (and their products, lists, options); a code on which `Encodable.decode` returns `none` is malformed; reason: the derived encoding is injective with a total, structurally recursive decoder; computability classes of predicates on ℕ do not depend on which such encoding is fixed
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 6.2, printed p. 25 / PDF p. 27

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 6.2 (Exact prefixes)** (printed p. 25 / PDF p. 27). For every well-formed `G`, closed
ground `t` and finite address `w`, the reader `read_G(t, w)` terminates and returns exactly the
label, bottom node or absence at `w` in `BT_G(t)`. Consequently the exact prefixes
`Pref(G, t, d)` of every finite depth `d` are total computable from the codes of `G`, `t` and `d`. -/
theorem lemma_6_2 :
    (∀ G : HORS, G.Valid → ∀ t : Tm, G.typeOf [] t = some .o →
      ∀ w : List ℕ, G.read t w = Part.some (G.BTat t w)) ∧
    ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d) := by sorry

end TreeEquivalenceHORS.Equivalence
