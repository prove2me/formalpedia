-- Prove2me | Theorems.Thm_UnderstandingML_natarajan_lemma
-- name    : UnderstandingML.natarajan_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:57:28.592976+00:00
-- url     : https://prove2.me/theorems/3f094d73-408a-4135-821a-8cda18bf26ab
-- title:
--   Lemma 29.4 (Natarajan): |H| ≤ |X|^{Ndim(H)} k^{2 Ndim(H)} for a class of functions from a finite X to [k]
-- statement:
--   **Lemma 29.4 (Natarajan).** $|H| \le |X|^{\operatorname{Ndim}(H)} \cdot k^{2\operatorname{Ndim}(H)}$.
--
--   Formally: for a finite domain $X$, a finite label set of size $k$, and $\operatorname{Ndim}(H) = d$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.2.1 p. 404, Lemma 29.4

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 29.4 (Natarajan)** (p. 404). For a class `H` of functions from a finite domain `X`
to `[k]`, `|H| ≤ |X|^{Ndim(H)} · k^{2 Ndim(H)}`. -/
theorem natarajan_lemma {X Y : Type*} [Fintype X] [Fintype Y] (H : Set (X → Y)) (d : ℕ)
    (hd : ndim H = d) :
    H.ncard ≤ Fintype.card X ^ d * Fintype.card Y ^ (2 * d) := by sorry

end UnderstandingML
