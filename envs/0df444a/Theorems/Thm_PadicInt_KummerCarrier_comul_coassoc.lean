-- Prove2me | Theorems.Thm_PadicInt_KummerCarrier_comul_coassoc
-- name    : PadicInt.KummerCarrier.comul_coassoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/662aa0ff-b9c8-5cb9-9323-3d2d8de49530
-- title:
--   Coassociativity of the Kummer carrier comultiplication
-- statement:
--   Let $p$ be a prime and let $u$ be a unit of the ring $\mathbb{Z}_p$ of $p$-adic integers. Write $H =$ `Carrier p u` for the $\mathbb{Z}_p$-algebra $\prod_{j \in \mathbb{Z}/p} A\,p\,u\,j$, the product over the residues $j$ modulo $p$ of the $\mathbb{Z}_p$-algebras `A p u j`, and let $\Delta =$ `Δ p u` be the $\mathbb{Z}_p$-algebra homomorphism $H \to H \otimes_{\mathbb{Z}_p} H$ attached to these data. The assertion is an equality of two $\mathbb{Z}_p$-algebra homomorphisms $H \to H \otimes_{\mathbb{Z}_p} (H \otimes_{\mathbb{Z}_p} H)$. The first is $\Delta$ followed by $\Delta \otimes \mathrm{id}_H$ and then by the associativity isomorphism $(H \otimes H) \otimes H \xrightarrow{\sim} H \otimes (H \otimes H)$ of `Algebra.TensorProduct.assoc`; the second is $\Delta$ followed by $\mathrm{id}_H \otimes \Delta$. Thus coassociativity of $\Delta$ is stated in the form required when the tensor products are not taken to be strictly associative, with the associator inserted on the left-hand composite.
--
--   This is the coassociativity axiom for the comultiplication on the Kummer carrier algebra over $\mathbb{Z}_p$, in the shape needed to build a bialgebra (and hence Hopf algebra) structure on it. It is used as one conjunct of [`PadicInt.KummerCarrier.bialgebra_axioms`](thm.html#PadicInt.KummerCarrier.bialgebra_axioms), which packages the comultiplication, counit and their compatibilities for the finite flat group scheme of order $p$ attached to the pair $(p, u)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_KummerCarrier_comul_coassoc.lean

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in
open PadicInt.KummerCarrier in

theorem PadicInt.KummerCarrier.comul_coassoc (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    (Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p]
        (Carrier p u) (Carrier p u) (Carrier p u)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Δ p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u))
      = (Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (Δ p u)).comp (Δ p u) := by sorry
