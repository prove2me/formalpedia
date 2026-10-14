-- Prove2me | Theorems.Thm_SelmerGroup_selmer_exact_sequence
-- name    : SelmerGroup.selmer_exact_sequence
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T15:58:26.260339+00:00
-- url     : https://prove2.me/theorems/a37122cc-660d-4912-9bac-10a7c2bba461
-- title:
--   $0\to E(K)/nE(K)\to\mathrm{Sel}^{(n)}(E/K)\to\text{Ш}(E/K)[n]\to0$
-- statement:
--   Let $K$ be a number field, $E/K$ an elliptic curve and $n\ge1$. There is an injective homomorphism
--   $$\delta: E(K)/nE(K)\hookrightarrow H^1(G_K,E(\bar K)[n])$$
--   such that
--
--   1. $\delta$ is the Kummer map: for every $P\in E(K)$ the class $\delta(P\bmod nE(K))$ is represented by $\sigma\mapsto\sigma Q-Q$ for some $Q\in E(\bar K)$ with $nQ=P$;
--   2. the image of $\delta$ is $\{\xi\in\mathrm{Sel}^{(n)}(E/K): j(\xi)=0\}$, where $j:H^1(G_K,E[n])\to H^1(G_K,E)$ is induced by inclusion;
--   3. $j$ maps $\mathrm{Sel}^{(n)}(E/K)$ onto $\text{Ш}(E/K)[n]$.
--
--   Equivalently, the sequence $0\to E(K)/nE(K)\xrightarrow{\delta}\mathrm{Sel}^{(n)}(E/K)\xrightarrow{j}\text{Ш}(E/K)[n]\to0$ is exact.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib
import Definitions.Def_SelmerGroup_ContinuousH1
import Definitions.Def_SelmerGroup_GaloisPoints
import Definitions.Def_SelmerGroup_Selmer

open NumberField

namespace SelmerGroup
theorem selmer_exact_sequence {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    [E.IsElliptic] (n : ℕ) (hn : 0 < n) :
    ∃ δ : Pts E K ⧸ (nsmulAddMonoidHom n : Pts E K →+ Pts E K).range →+ H1 (absTorsAct E K n),
      Function.Injective δ ∧
      (∀ P : Pts E K, ∃ c : cocycles (absTorsAct E K n),
        H1.mk (absTorsAct E K n) c = δ (QuotientAddGroup.mk P) ∧
        ∃ Q : Pts E (AlgebraicClosure K),
          n • Q = ptsMap E (IsScalarTower.toAlgHom K K (AlgebraicClosure K)) P ∧
          ∀ σ, (c.1 σ : Pts E (AlgebraicClosure K)) = absAct E K σ Q - Q) ∧
      Set.range δ = {ξ | ξ ∈ selmerGroup E n ∧ torsInclH1 E K n ξ = 0} ∧
      torsInclH1 E K n '' selmerGroup E n = shaTors E n := by sorry
end SelmerGroup
