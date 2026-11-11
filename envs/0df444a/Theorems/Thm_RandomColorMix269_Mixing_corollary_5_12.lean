-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_corollary_5_12
-- name    : RandomColorMix269.Mixing.corollary_5_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:25.616609+00:00
-- url     : https://prove2.me/theorems/50417896-e541-4330-9312-712a79c23dd1
-- title:
--   Corollary 5.12 — $\nu=\mu_U$ and all coordinate marginals of its conditionals have connected conditional supports
-- statement:
--   Let $G$ be a finite graph, $D,q$ integers with $q-D\ge2$, $S=N_G[V^{HD}]$ for the cutoff $D$ and $U=V\setminus S$. Assume the extension property: every proper $q$-colouring of $G[U]$ extends to a proper $q$-colouring of $G$. Then $\nu=(\mu_{G,q})_U$ has connected conditional supports. Moreover, for every feasible pinning $\tau$ of $\nu$ and every $W\subseteq U$, the coordinate marginal $(\nu^\tau)_W$ also has connected conditional supports.
--
--   Connected conditional supports is one of the three hypotheses of Theorem 5.7 and of Lemma 5.6.
--
--   Differences from the source:
--   - generalization: G ∼ G(n,d/n) with D = ⌊(1+η/3)d⌋ (§5.3 context) → any finite graph G on any finite vertex type and any cutoff D; reason: the statement and its proof use only q − D ≥ 2 and the extension property; it specializes to the source's G and D
--   - encoding: every coordinate marginal of a feasible conditional distribution of ν → the marginal of ν^τ onto every W ⊆ U, for every feasible τ; reason: reading of 'coordinate marginal' as projection to a coordinate subset
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.33, Corollary 5.12

import Definitions.Def_RandomColorMix269_Mixing_Parameters

open scoped Classical BigOperators
open Finset
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Corollary 5.12, p.33. Includes every coordinate marginal after every feasible pin. -/
theorem corollary_5_12 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q D : ℕ) (hslack : D + 2 ≤ q)
    (hext : ExtensionProperty G q (lowRegion G D)) :
    ConnectedConditionalSupports (bufferedLaw G q D) ∧
      ∀ (Λ : Finset (lowRegion G D)) (x : lowRegion G D → Fin q),
        Feasible (bufferedLaw G q D) Λ x → ∀ W : Finset (lowRegion G D),
          ConnectedConditionalSupports (marginal (SpinGirth5.pin (bufferedLaw G q D) Λ x) W) := by sorry

end RandomColorMix269.Mixing
