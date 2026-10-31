-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P41_authentication_standard
-- name    : QAlgorithms.Papers.Independent.Intake100.P41.authentication_standard
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:21:09.25356+00:00
-- url     : https://prove2.me/theorems/cc3ade4a-0205-4987-b5bd-dcefb81c7682
-- title:
--   Composable security of standard authentication under the pair-only ASU2 convention
-- statement:
--   Let $K$ and $T$ be finite nonempty key and tag sets, and let the message alphabet $X$ contain at least two elements. Let $\varepsilon\ge0$, and suppose a uniform $k\in K$ satisfies, for all distinct $x,y\in X$ and all $a,b\in T$,
--
--   $$
--   \Pr[h_k(x)=a\ \text{and}\ h_k(y)=b]\le\frac{\varepsilon}{|T|}.
--   $$
--
--   No marginal-uniformity condition is assumed. Alice sends $(x,h_k(x))$; Bob accepts a submitted pair $(x',t')$ exactly when $t'=h_k(x')$. Let $R$ be this real resource and $A$ the ideal authentic channel that reveals Alice's message and permits delivery or suppression. There is a fixed simulator with
--
--   $$
--   d(R_{\rm hon},A_{\rm hon})=0,\qquad d(R,A\sigma)\le\varepsilon.
--   $$
--
--   This includes both input orders and arbitrary adaptive later inputs. For substitution the simulator samples its own uniform hash key; after an impersonation-first rejection, it samples uniformly among keys that reject that submitted pair before producing a later honest tag. If that conditioning set is empty, it falls back to the unconditioned uniform law; the corresponding real rejection event is impossible.
--
--   The conclusion is full resource security rather than only an impersonation or substitution probability bound. The distinct-message convention is essential when deriving single-tag security from the source's pair-only definition.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, PDF p. 17, Lemma 9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7--9,17--18, Lemma 9: the source's pair-only ASU2 condition yields
full epsilon resource security, including impersonation and substitution with
arbitrary subsequent inputs. Nontrivial X is required by the appendix's choice
of a distinct message; no single-tag uniformity assumption is inserted. -/
theorem authentication_standard {K X T : Type*} [Fintype K] [Nonempty K]
    [Fintype T] [Nonempty T] [Nontrivial X] (h : K → X → T) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hh : IsASU2 h epsilon) :
    StandardConstructionSecure h epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P41

end
