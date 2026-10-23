-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_lemma_7_6
-- name    : WalledBrauer.SuperSchurWeyl.lemma_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:15.209063+00:00
-- url     : https://prove2.me/theorems/8f95f6c8-56f6-444e-a4da-f2318504b23e
-- title:
--   Lemma 7.6 (restated as its instance (7.16)) — flip_{r,s} : End(V^{⊗(r+s)}) → End(V^{⊗r} ⊗ W^{⊗s}) is a g-isomorphism
-- statement:
--   Let $m, n, r, s \ge 0$ and $\mathfrak g = \mathfrak{gl}_{m|n}(\mathbb C)$. Let
--
--   $$
--   \mathrm{flip}_{r,s} : \operatorname{End}(V^{\otimes(r+s)}) \to \operatorname{End}(V^{\otimes r} \otimes W^{\otimes s})
--   $$
--
--   be the map of (7.16): under $\operatorname{End}(V^{\otimes(r+s)}) = \operatorname{End}(V^{\otimes r}) \otimes \operatorname{End}(V^{\otimes s})$ and $\operatorname{End}(V^{\otimes r} \otimes W^{\otimes s}) = \operatorname{End}(V^{\otimes r}) \otimes \operatorname{End}(W^{\otimes s})$ it is $f \otimes g \mapsto f \otimes g^*$ (with $W^{\otimes s} = (V^{\otimes s})^*$ as in (7.15)). Then $\mathrm{flip}_{r,s}$ is an isomorphism of $\mathfrak g$-supermodules:
--
--   1. it is bijective;
--   2. it intertwines the actions of $\mathfrak g$ on the two spaces of endomorphisms, $(xf)(u) = x(f(u)) - (-1)^{|x||f|} f(xu)$: for every matrix unit $e_{a,b}$ and every $X$,
--   $$
--   \mathrm{flip}_{r,s}(e_{a,b} \cdot X) = e_{a,b} \cdot \mathrm{flip}_{r,s}(X);
--   $$
--   3. consequently it maps $\operatorname{End}_{\mathfrak g}(V^{\otimes(r+s)})$ onto $\operatorname{End}_{\mathfrak g}(V^{\otimes r} \otimes W^{\otimes s})$.
--
--   Lemma 7.6 of the paper asserts this for $\mathrm{Hom}(M \otimes K, N \otimes L) \to \mathrm{Hom}(M \otimes L^*, N \otimes K^*)$ and arbitrary finite-dimensional $\mathfrak g$-supermodules $K, L, M, N$; this item is its instance $M = N = V^{\otimes r}$, $K = L = V^{\otimes s}$ stated on p. 54, which is the only instance the proof of Theorem 7.8 uses.
--
--   **Formalization Note** `flipEnd m n r s` is $\mathrm{flip}_{r,s}$ in coordinates (see the `TensorSpace` definition); `adE κ a b` is the action of $e_{a,b}$ on $\operatorname{End}$. Intertwining the spanning set $\{e_{a,b}\}$ is equivalent to intertwining all of $\mathfrak g$. The general statement for arbitrary supermodules is not posed, as Mathlib has no category of supermodules.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 54, Lemma 7.6 and its instance (7.16), with (7.13) (p. 53), (7.15) (p. 54), (7.18) (p. 55)

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

/-- Lemma 7.6 (p. 54), restated as its instance (7.16): `flip_{r,s} : End(V^{⊗(r+s)}) →
End(V^{⊗ r} ⊗ W^{⊗ s})` is a `g`-supermodule isomorphism: it is bijective and intertwines the
action of every matrix unit `e_{a,b}` on `End`; consequently it maps `End_g(V^{⊗(r+s)})`
onto `End_g(V^{⊗ r} ⊗ W^{⊗ s})`. -/
theorem lemma_7_6 (m n r s : ℕ) :
    Function.Bijective (flipEnd m n r s) ∧
    (∀ (a b : Fin (m + n)) (X : Op m n (r + s)),
        flipEnd m n r s (adE m n (allV (r + s)) a b X) =
          adE m n (mixed r s) a b (flipEnd m n r s X)) ∧
    (EndG m n (allV (r + s))).map (flipEnd m n r s) = EndG m n (mixed r s) := by sorry

end WalledBrauer.SuperSchurWeyl
