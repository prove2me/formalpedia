-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P59_twisting_equivalence
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P59.twisting_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:48:26.648182+00:00
-- url     : https://prove2.me/theorems/75fbd1e1-a598-42e4-a07f-bdd866497647
-- title:
--   Twisting gauges characterize principal simplicial bundle isomorphisms
-- statement:
--   Let $G$ be a simplicial group and $X$ a simplicial set. Let $\tau_n,\tau'_n:X_n\to G_{n-1}$, for $n\geq 1$, be twistings satisfying all four identities of Section 1.1. Their principal left bundles have degree-$n$ spaces $P(\tau)_n=G_n\times X_n$, componentwise degeneracies and positive faces, and zeroth face $d_0(g,x)=(d_0g\,\tau_n(x),d_0x)$.
--
--   A family $\psi_n:X_n\to G_n$ is a gauge precisely when, for every applicable degree and index,
--
--   $$
--   d_0\psi_n(x)\,\tau'_n(x)=\tau_n(x)\,\psi_{n-1}(d_0x),\qquad
--   d_i\psi_n(x)=\psi_{n-1}(d_ix)\ (i>0),\qquad
--   s_i\psi_n(x)=\psi_{n+1}(s_ix).
--   $$
--
--   Every such family gives an equivariant bundle isomorphism over $X$, commuting with every face and degeneracy, with degreewise formula
--
--   $$
--   \Phi_n(g,x)=(g\,\psi_n(x),x).
--   $$
--
--   Conversely, every equivariant simplicial bundle isomorphism $P(\tau)\to P(\tau')$ over $X$ has this formula for a family satisfying the displayed gauge laws. Thus these laws characterize equivalence of the two principal bundles.
--
--   **Formalization Note** The source calls $\psi$ simplicial, but its displayed zeroth-face equation replaces ordinary zeroth-face naturality. The statement uses those displayed equations; imposing both would change the result.
-- source:
--   Crossed Module Bundle Gerbes; Classification, String Group and Differential Geometry, arXiv:math/0510078v2, PDF p. 4, Section 1.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P59

open CategoryTheory

open scoped Simplicial

universe u

namespace QAlgorithms.Papers.Independent.Intakenext100.P59

/-- Section 1.3, PDF p. 4: gauges are exactly the equivalences of the two
principal twisted bundles. A gauge from tau to tauPrime acts by
(g,x) |-> (g * psi(x),x). Correction to the source: "simplicial map psi" means
the displayed twisted zeroth-face law together with the other naturality laws,
not ordinary naturality in addition to those laws. -/
theorem twisting_equivalence
    (G : SimplicialObject GrpCat.{u}) (X : SSet.{u}) (tau tauPrime : Twisting G X) :
    (∀ psi : TwistingGauge tau tauPrime,
      ∃ e : TwistedBundleIso tau tauPrime,
        ∀ (n : ℕ) (p : TwistedPoint G X n),
          e.map n p = (p.1 * psi.value n p.2, p.2)) ∧
    (∀ e : TwistedBundleIso tau tauPrime,
      ∃ psi : TwistingGauge tau tauPrime,
        ∀ (n : ℕ) (p : TwistedPoint G X n),
          e.map n p = (p.1 * psi.value n p.2, p.2)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P59
