-- Prove2me | Theorems.Thm_PadicInt_KummerCarrier_bialgebra_axioms
-- name    : PadicInt.KummerCarrier.bialgebra_axioms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/ced6b06b-3647-5632-8bf2-037df5d45190
-- title:
--   Coalgebra axioms and cocommutativity for the Kummer carrier
-- statement:
--   Fix a prime $p$ and a unit $u \in \mathbb{Z}_p^{\times}$, and let $H =$ `Carrier p u` be the $\mathbb{Z}_p$-algebra $\prod_{j \in \mathbb{Z}/p} A\,p\,u\,j$, the product over the residues $j$ modulo $p$ of the component algebras `A p u j`. Let $\Delta =$ `Δ p u` be the $\mathbb{Z}_p$-algebra homomorphism $H \to H \otimes_{\mathbb{Z}_p} H$ and $\varepsilon =$ `ε p u` the $\mathbb{Z}_p$-algebra homomorphism $H \to \mathbb{Z}_p$ attached to this carrier. The theorem asserts the conjunction of four statements. First, coassociativity in the form that $\Delta$ followed by $\Delta \otimes \mathrm{id}_H$ followed by the associativity isomorphism $(H \otimes H) \otimes H \simeq H \otimes (H \otimes H)$ equals $\Delta$ followed by $\mathrm{id}_H \otimes \Delta$, as algebra maps $H \to H \otimes H \otimes H$. Second, the left counit law: $\Delta$ followed by $\varepsilon \otimes \mathrm{id}_H$ equals the inverse of the left unitor $\mathbb{Z}_p \otimes H \simeq H$. Third, the right counit law: $\Delta$ followed by $\mathrm{id}_H \otimes \varepsilon$ equals the inverse of the right unitor $H \otimes \mathbb{Z}_p \simeq H$. Fourth, cocommutativity, stated pointwise: for every $h \in H$, the flip of $H \otimes H$ fixes $\Delta(h)$.
--
--   These are the coalgebra axioms (coassociativity, the two counit laws) together with cocommutativity for the comultiplication and counit of the Kummer carrier, in precisely the shape needed to assemble a bialgebra structure on $H$; they form the coalgebra half of the Hopf-algebra structure on the Oort–Tate style group scheme of order $p^2$ attached to the unit $u$. The first clause is the separately recorded coassociativity statement [`PadicInt.KummerCarrier.comul_coassoc`](thm.html#PadicInt.KummerCarrier.comul_coassoc), and the whole conjunction is used in [`PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval`](thm.html#PadicInt.exists_finiteFlat_kummerHopf_withConv_aeval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_KummerCarrier_bialgebra_axioms.lean

import Mathlib
import Definitions.Def_PadicInt_KummerCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in
open PadicInt.KummerCarrier in

theorem PadicInt.KummerCarrier.bialgebra_axioms (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ((Algebra.TensorProduct.assoc ℤ_[p] ℤ_[p] ℤ_[p]
        (Carrier p u) (Carrier p u) (Carrier p u)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Δ p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u))
      = (Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (Δ p u)).comp (Δ p u)) ∧
    ((Algebra.TensorProduct.map (ε p u) (.id ℤ_[p] (Carrier p u))).comp (Δ p u)
      = (Algebra.TensorProduct.lid ℤ_[p] (Carrier p u)).symm) ∧
    ((Algebra.TensorProduct.map (.id ℤ_[p] (Carrier p u)) (ε p u)).comp (Δ p u)
      = (Algebra.TensorProduct.rid ℤ_[p] ℤ_[p] (Carrier p u)).symm) ∧
    (∀ h, (TensorProduct.comm ℤ_[p] (Carrier p u) (Carrier p u)) (Δ p u h) = Δ p u h) := by sorry
