-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_lemma_2_6
-- name    : ScatCaps.LinearSets.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:59.376229+00:00
-- url     : https://prove2.me/theorems/a0b49bd3-dd4e-4156-ba76-48d303d7b639
-- title:
--   Lemma 2.6, p. 11 — φ(x)/x and φ̄(x)/x have the same image on 𝔽*_{q^{3n}}
-- statement:
--   Throughout, $q=p^h$ is a prime power, $n\ge2$, and $E=\mathbb F_{q^{6n}}$. For $m\in\{1,n,2n,3n\}$, $\mathbb F_{q^m}$ denotes the unique subfield of $E$ of order $q^m$, and $\mathbb F_{q^m}^*=\mathbb F_{q^m}\setminus\{0\}$. The field $E$ is a $3$-dimensional vector space over $\mathbb F_{q^{2n}}$, and $\mathbb P=\mathrm{PG}(\mathbb F_{q^{6n}},\mathbb F_{q^{2n}})=\mathrm{PG}(2,q^{2n})$ is the associated projective plane: its points are the $\mathbb F_{q^{2n}}$-spans $\langle v\rangle_{\mathbb F_{q^{2n}}}$ of nonzero $v\in E$.
--
--   Every $\mathbb F_q$-linear map of $\mathbb F_{q^{3n}}$ has the form $\varphi(x)=\sum_{i=0}^{3n-1}a_ix^{q^i}$ with $a_i\in\mathbb F_{q^{3n}}$. Its adjoint with respect to the non-degenerate symmetric bilinear form $\langle x,y\rangle=\mathrm{Tr}_{q^{3n}/q}(xy)$ is
--
--   $$
--   \bar\varphi(x)=\sum_{i=0}^{3n-1}a_i^{q^{3n-i}}x^{q^{3n-i}} .
--   $$
--
--   Lemma 2.6 states that the maps $x\mapsto\varphi(x)/x$ and $x\mapsto\bar\varphi(x)/x$ have the same image:
--
--   $$
--   \Big\{\frac{\varphi(x)}{x}: x\in\mathbb F_{q^{3n}}^*\Big\}=\Big\{\frac{\bar\varphi(x)}{x}: x\in\mathbb F_{q^{3n}}^*\Big\}.
--   $$
--
--   The lemma is used in the proof of Proposition 2.7 to transfer condition (16) from $f_{i,a,b}$ to its adjoint.
--
--   **Formalization Note** $\varphi$ is given by its coefficient vector $(a_0,\dots,a_{3n-1})$ in $\mathbb F_{q^{3n}}$ and $\bar\varphi$ by the printed formula (p. 11, top); the field tower is that of §2. Exponents $3n-i$ are natural-number subtractions with $i<3n$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, pp. 10–11, adjoint formula and Lemma 2.6

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem lemma_2_6 (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) [ExpChar E p] (hs : Section2Setting E p h q n)
    (a : Fin (3 * n) → E) (ha : ∀ i, a i ∈ subfieldOf E p h (3 * n)) :
    {z : E | ∃ x : E, x ∈ subfieldOf E p h (3 * n) ∧ x ≠ 0 ∧
        z = linearized q n a x / x} =
      {z : E | ∃ x : E, x ∈ subfieldOf E p h (3 * n) ∧ x ≠ 0 ∧
        z = adjoint q n a x / x} := by sorry

end ScatCaps.LinearSets
