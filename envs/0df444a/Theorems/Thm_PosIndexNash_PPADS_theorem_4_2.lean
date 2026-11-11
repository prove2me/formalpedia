-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_theorem_4_2
-- name    : PosIndexNash.PPADS.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:32:48.892344+00:00
-- url     : https://prove2.me/theorems/9ac04817-8263-4105-ba43-2a35cc7a1bf1
-- title:
--   Theorem 4.2 — indexed fixed point map: a polynomial-time Linear-FIXP circuit whose fixed points are the sinks (+1) and noncanonical sources (−1)
-- statement:
--   Given a normalized Sink-of-Line instance $S, P : \{0,1\}^n \to \{0,1\}^n$, one can construct in polynomial time a rational Linear-FIXP circuit for a map $\Phi : [0,1]^2 \to [0,1]^2$ such that, with $H$ the graph (Graph):
--
--   1. the fixed points of $\Phi$ correspond bijectively to the sinks and noncanonical sources of $H$;
--   2. every fixed point $p$ is regular ($\det(I_2 - D\Phi(p)) \ne 0$), lies in the interior $(0,1)^2$, and makes every max gate strict;
--   3. the fixed point index is $+1$ at a sink and $-1$ at a noncanonical source:
--   $$\mathrm{ind}_\Phi(p) = \mathrm{sign}\det(I_2 - D\Phi(p)) = \begin{cases} +1 & p \leftrightarrow \text{sink},\\ -1 & p \leftrightarrow \text{noncanonical source};\end{cases}$$
--   4. every fixed point of positive index decodes in polynomial time to an $x \in \{0,1\}^n$ with $P(S(x)) \ne x$.
--
--   In Lean: there are polynomial-time maps `construct` (instance code ↦ circuit code) and `decode` such that for every normalized instance the constructed circuit is well formed with two inputs and two outputs, maps $[0,1]^2$ into itself, and there is an explicit bijection `e` from its fixed points in $[0,1]^2$ to the sinks and noncanonical sources with properties 2–4; in 4, a positive-index fixed point is a rational point $q$ and `decode` applied to the instance code paired with the code of $q$ returns $x$.
--
--   Differences from the source:
--   - encoding: circuits and "construct in polynomial time" → the binary code `LinCircuit.enc` and a map `construct` computable in polynomial time on Cook's Turing machines with `construct (encCircuit S ++ encCircuit P) = C.enc`; reason: standard encoding of the construction.
--   - reading: "every positive index fixed point decodes in polynomial time to x" → every positive-index fixed point is a rational point $q$ and a fixed polynomial-time `decode`, given the instance code and `encRatVec 2 q`, returns $x$ of length $n$ with $P(S(x)) \ne x$; reason: a decoder reads a binary representation, and the fixed points are rational barycenters (p. 34).
--   - encoding: $D\Phi(p)$, the Jacobian of the active affine piece → the Fréchet derivative of the circuit's map on $\mathbb{R}^2$; reason: at a strict point $\Phi$ equals its active piece near $p$ (p. 13), so they coincide.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), pp. 19–20, Theorem 4.2

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_Circuit
import Definitions.Def_ConstrSOSP_Circuit_eval
import Definitions.Def_ConstrSOSP_encCircuit
import Definitions.Def_PosIndexNash_PPADS_SinkOfLine
import Definitions.Def_PosIndexNash_PPADS_GraphH
import Definitions.Def_PosIndexNash_PPADS_LinCircuit
import Definitions.Def_PosIndexNash_PPADS_FixedPointIndex

namespace PosIndexNash.PPADS

theorem theorem_4_2 :
    ∃ (construct : List Bool → List Bool) (decode : List (Option (Bool ⊕ Bool)) → List Bool),
      CookPvsNP.PolyTimeComputable construct ∧ CookPvsNP.PolyTimeComputable decode ∧
      ∀ S P : ConstrSOSP.Circuit, IsSOLInstance S P →
        ∃ C : LinCircuit, C.WF ∧ C.dIn = 2 ∧ C.outs.length = 2 ∧
          construct (ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P) = C.enc ∧
          (∀ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
            ∀ i, 0 ≤ C.toMap 2 x i ∧ C.toMap 2 x i ≤ 1) ∧
          ∃ e : {p : Fin 2 → ℝ // (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ C.toMap 2 p = p} ≃
              {u : List Bool // IsHSink S P u ∨ IsHNoncanonicalSource S P u},
            (∀ p : {p : Fin 2 → ℝ // (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ C.toMap 2 p = p},
              IsRegularFixedPoint (C.toMap 2) p.1 ∧ C.StrictAt p.1) ∧
            (∀ p : {p : Fin 2 → ℝ // (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ C.toMap 2 p = p},
              IsHSink S P (e p).1 → fixedPointIndex (C.toMap 2) p.1 = 1) ∧
            (∀ p : {p : Fin 2 → ℝ // (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ C.toMap 2 p = p},
              IsHNoncanonicalSource S P (e p).1 → fixedPointIndex (C.toMap 2) p.1 = -1) ∧
            (∀ p : {p : Fin 2 → ℝ // (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ C.toMap 2 p = p},
              fixedPointIndex (C.toMap 2) p.1 = 1 →
              ∃ q : Fin 2 → ℚ, (p.1 = fun i => (q i : ℝ)) ∧
                (decode ((ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P).map
                    (some ∘ Sum.inl) ++
                  none :: (CardinalMatching.encRatVec 2 q).map (some ∘ Sum.inr))).length = S.n ∧
                P.eval (S.eval (decode ((ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P).map
                    (some ∘ Sum.inl) ++
                  none :: (CardinalMatching.encRatVec 2 q).map (some ∘ Sum.inr)))) ≠
                  decode ((ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P).map
                    (some ∘ Sum.inl) ++
                  none :: (CardinalMatching.encRatVec 2 q).map (some ∘ Sum.inr))) := by sorry

end PosIndexNash.PPADS
