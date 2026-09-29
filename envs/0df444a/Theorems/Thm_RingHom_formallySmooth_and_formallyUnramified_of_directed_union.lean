-- Prove2me | Theorems.Thm_RingHom_formallySmooth_and_formallyUnramified_of_directed_union
-- name    : RingHom.formallySmooth_and_formallyUnramified_of_directed_union
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/dc3faf66-fc4e-5d6f-a18d-4790e959d0d6
-- title:
--   Formal smoothness and unramifiedness pass to directed unions
-- statement:
--   Let $\iota$ be a nonempty index type equipped with a relation $r$ that is directed in the sense that any two indices $i,j$ admit a $k$ with $r\,i\,k$ and $r\,j\,k$. Let $A$ and $S$ be commutative rings, and let $(A_i)_{i\in\iota}$, $(S_i)_{i\in\iota}$ be families of commutative rings with ring homomorphisms $a_i : A_i \to A$ and $s_i : S_i \to S$, each $s_i$ injective, together with transition homomorphisms $a_{ij} : A_i \to A_j$ and $s_{ij} : S_i \to S_j$ for every $h : r\,i\,j$ satisfying $a_j \circ a_{ij} = a_i$ and $s_j \circ s_{ij} = s_i$; assume every element of $A$ lies in the image of some $a_i$ and every element of $S$ in the image of some $s_i$. Let $\varphi_i : A_i[X] \to S_i$ be ring homomorphisms, each formally smooth and formally unramified, compatible with the transitions in the sense that $s_{ij} \circ \varphi_i = \varphi_j \circ A_{ij}[X]$, where $A_{ij}[X]$ denotes the coefficientwise map induced by $a_{ij}$. Finally let $\varphi : A[X] \to S$ be a ring homomorphism with $s_i \circ \varphi_i = \varphi \circ a_i[X]$ for all $i$. Then $\varphi$ is formally smooth and formally unramified.
--
--   This is the permanence of formal smoothness and formal unramifiedness (hence formal étaleness) under passage to a directed union of charts, in the special shape needed for polynomial-algebra presentations $A_i[X] \to S_i$. It is used in the construction of smooth point data for curves over directed towers of subfields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_formallySmooth_and_formallyUnramified_of_directed_union.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.formallySmooth_and_formallyUnramified_of_directed_union
    {ι : Type} [Nonempty ι] (r : ι → ι → Prop) (hdir : ∀ i j, ∃ k, r i k ∧ r j k)
    {A S : Type} [CommRing A] [CommRing S]
    (An Sn : ι → Type) [∀ i, CommRing (An i)] [∀ i, CommRing (Sn i)]
    (a : ∀ i, An i →+* A) (s : ∀ i, Sn i →+* S) (hs : ∀ i, Function.Injective (s i))
    (aa : ∀ i j, r i j → (An i →+* An j)) (ss : ∀ i j, r i j → (Sn i →+* Sn j))
    (haa : ∀ i j (h : r i j), (a j).comp (aa i j h) = a i) (hss : ∀ i j (h : r i j), (s j).comp (ss i j h) = s i)
    (hcovA : ∀ x : A, ∃ i y, a i y = x) (hcovS : ∀ x : S, ∃ i y, s i y = x)
    (φn : ∀ i, Polynomial (An i) →+* Sn i)
    (hφs : ∀ i, (φn i).FormallySmooth) (hφu : ∀ i, (φn i).FormallyUnramified)
    (hφn : ∀ i j (h : r i j), (ss i j h).comp (φn i) = (φn j).comp (Polynomial.mapRingHom (aa i j h)))
    (φ : Polynomial A →+* S) (hφ : ∀ i, (s i).comp (φn i) = φ.comp (Polynomial.mapRingHom (a i))) :
    φ.FormallySmooth ∧ φ.FormallyUnramified := by sorry
