-- Prove2me | Theorems.Thm_RingHom_BijectiveOnStalks_comp
-- name    : RingHom.BijectiveOnStalks.comp
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:28.084854+00:00
-- url     : https://prove2.me/theorems/e6ad22a5-0a75-51da-a756-2f3c51091852
-- title:
--   Ring maps that are bijective on stalks are closed under composition
-- statement:
--   A ring homomorphism $f:R\to S$ of commutative rings is called *bijective on stalks* if for every prime ideal $\mathfrak p\subset S$, the induced local homomorphism
--   $$R_{f^{-1}(\mathfrak p)} \longrightarrow S_{\mathfrak p}$$
--   is bijective. Let $f:R\to S$ and $g:S\to T$ be homomorphisms of commutative rings that are both bijective on stalks. Then the composite $g\circ f : R\to T$ is bijective on stalks.
--
--   This closure property is part of the basic theory of ring maps that identify local rings, which appear in the pro-étale project's treatment of ind-Zariski and w-local algebras.
--
--   **Formalization Note** `R : Type u`, `S : Type v`, `T : Type*`, all commutative rings. `RingHom.BijectiveOnStalks f` is defined in the fork as: for every prime `p : Ideal S`, `Localization.localRingHom (p.comap f) p f rfl` is bijective. The statement is `(g.comp f).BijectiveOnStalks`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/StalkIso.lean, lines 57-63 (`RingHom.BijectiveOnStalks.comp`).

import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Algebra_StalkIso

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom
namespace BijectiveOnStalks

theorem comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.BijectiveOnStalks) (hg : g.BijectiveOnStalks) : (g.comp f).BijectiveOnStalks := by sorry

end BijectiveOnStalks
end RingHom
