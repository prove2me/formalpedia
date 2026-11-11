-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_2_16_nonwitnessing
-- name    : SAInterp.Res2.theorem_2_16_nonwitnessing
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:38:47.606461+00:00
-- url     : https://prove2.me/theorems/3b746486-cb04-4e04-8841-b43cb9286936
-- title:
--   §2.3, proof of Theorem 2.16 — if D is F-nonwitnessing then D^bool is F^bool-nonwitnessing
-- statement:
--   Let $X=\{(x_v,S_v)\}$ be a finite collection of multivalued variables with $|S_v|=2^{w_v}$, let $D$ be a degree-$d$ indicator design on $A(X)$, and let $F$ be a multivalued CNF over $X$. Suppose $D$ is $F$-nonwitnessing: $D[C]=0$ for every clause $C_i\in F$ and every indicator conjunction $C\Rightarrow\bar C_i$ with $\mathrm{bdeg}(C)\le d$. Then $D^{\mathrm{bool}}$ is $F^{\mathrm{bool}}$-nonwitnessing:
--   $$D^{\mathrm{bool}}[C]=0\quad\text{for every clause }C'_i\in F^{\mathrm{bool}}\text{ and every boolean conjunction }C\Rightarrow\bar C'_i\text{ with }\deg C\le d.$$
--   The paper records this in the proof of Theorem 2.16, and Theorem 8.1 uses it.
--
--   Differences from the source:
--   - reading: the sentence "if D is non-witnessing for some F, then D^bool is non-witnessing for F^bool" in the proof of Theorem 2.16 → a standalone statement with the proof's hypotheses (|S_v| = 2^{w_v}, D a degree-d indicator design) and F^bool the binary encoding of F (Definition 2.15's encoding, as for CPLS^bool_n); reason: it is the transfer Theorem 8.1 needs, and the paper states it only inside the proof.
--   - encoding: binary encoding and D^bool as in Theorem 2.16 (`Fin (size v)`, `testBit`, powers read as their base); reason: Lean convention, same objects.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 22 (PDF p. 24), §2.3, proof of Theorem 2.16

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams
import Definitions.Def_SAInterp_Res2_Indicator

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- §2.3, proof of Theorem 2.16 (p. 22): if the degree-`d` indicator design `D` is
`F`-nonwitnessing for a multivalued CNF `F`, then `D^bool` is `F^bool`-nonwitnessing. -/
theorem theorem_2_16_nonwitnessing {V : Type} [Fintype V] (size w : V → ℕ)
    (hw : ∀ v, size v = 2 ^ w v) (d : ℕ) (D : IndAlg size → ℝ) (hD : IsIndicatorDesign d D)
    (F : MVCNF size) (hF : IsIndNonwitnessing F d D) :
    IsNonwitnessing (cnfBool w F) d (booleanization w D) := by sorry

end SAInterp.Res2
