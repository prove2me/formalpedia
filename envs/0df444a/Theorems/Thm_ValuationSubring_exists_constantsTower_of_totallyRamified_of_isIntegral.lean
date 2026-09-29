-- Prove2me | Theorems.Thm_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral
-- name    : ValuationSubring.exists_constantsTower_of_totallyRamified_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/e59c6196-93fa-5768-b210-0d63e5bcbd54
-- title:
--   Extending a valuation along a totally ramified constant field extension
-- statement:
--   Let $k$ be a field of characteristic $0$ and $F$ a field with a $k$-algebra structure, and let $L$ and $F_0$ be intermediate fields of $F/k$ with $L \sqcup F_0 = \top$, i.e. generating $F$ together. Let $A$ be a valuation subring of $L$ and $W_0$ a valuation subring of $F_0$ which agree on $k$, in the sense that for each $x \in k$ one has $\mathrm{alg}_{k,L}(x) \in A$ if and only if $\mathrm{alg}_{k,F_0}(x) \in W_0$. Assume $W_0$ is a discrete valuation ring, and that there is $\pi_0 \in k$ whose image lies in $W_0$ and generates the maximal ideal of $W_0$. Assume further that every element of $A$ is integral over the valuation subring $A \cap k$ of $k$ (the comap of $A$ along $k \to L$), and the following approximation hypothesis: for every finite subset $s$ of $L$ there are an integer $n > 0$, an element $\varpi' \in A$ and a unit $u$ of $A$ (given with its inverse $v$) such that every element of $s$ lies in the intermediate field $k(\varpi')$ of $F$, $[k(\varpi') : k] = n$, $\varpi'^{\,n} = \pi_0 u$, and every non-zero $a \in A$ lying in $k(\varpi')$ has the form $a = \varpi'^{\,m} w$ for some $m \in \mathbb{N}$ and some unit $w$ of $A$. Then there exists a valuation subring $W$ of $F$ such that: an element of $L$ lies in $W$ exactly when it lies in $A$; an element of $F_0$ lies in $W$ exactly when it lies in $W_0$; every $w \in W$ is congruent modulo the maximal ideal of $W$ to (the image in $W$ of) an element of $W_0$; and for every non-zero $f \in F$ there is a non-zero $c \in L$ such that $cf \in W$ and $cf$ is a unit of $W$.
--
--   This is the extension of a discrete valuation of $F_0/k$ to the compositum $F = L \cdot F_0$ along a totally ramified algebraic extension $L/k$ of the constants, with the residue field unchanged and with every non-zero element of $F$ becoming a unit after scaling by a constant from $L$. It is used in the analysis of local behaviour of modular curves at nodes, where places of the function field are produced from a valuation on the constant field together with the branch or centre data of a crossing presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_constantsTower_of_totallyRamified_of_isIntegral
    (k F : Type) [Field k] [CharZero k] [Field F] [Algebra k F]
    (L F₀ : IntermediateField k F) (hgen : L ⊔ F₀ = ⊤)
    (A : ValuationSubring ↥L) (W₀ : ValuationSubring ↥F₀)
    (hagree : ∀ x : k, algebraMap k ↥L x ∈ A ↔ algebraMap k ↥F₀ x ∈ W₀)
    (hdvr : IsDiscreteValuationRing ↥W₀)
    (π₀ : k) (hπ₀ : algebraMap k ↥F₀ π₀ ∈ W₀)
    (hunif : maximalIdeal ↥W₀ = Ideal.span {(⟨algebraMap k ↥F₀ π₀, hπ₀⟩ : ↥W₀)})

    (hint : ∀ a : ↥L, a ∈ A → IsIntegral ↥(A.comap (algebraMap k ↥L)) a)

    (htower : ∀ s : Finset ↥L, ∃ (n : ℕ) (ϖ' : ↥L) (u v : ↥A), 0 < n ∧ ϖ' ∈ A ∧ (u : ↥L) * v = 1 ∧
        (∀ x ∈ s, (x : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) ∧
        Module.finrank k ↥(IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) = n ∧
        ϖ' ^ n = algebraMap k ↥L π₀ * (u : ↥L) ∧
        (∀ a : ↥L, a ∈ A → (a : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)} → a ≠ 0 →
          ∃ (m : ℕ) (w z : ↥A), (w : ↥L) * z = 1 ∧ a = ϖ' ^ m * (w : ↥L))) :
    ∃ W : ValuationSubring F,
      (∀ x : ↥L, (x : F) ∈ W ↔ x ∈ A) ∧
      (∀ f : ↥F₀, (f : F) ∈ W ↔ f ∈ W₀) ∧
      (∀ w : ↥W, ∃ (f : ↥W₀) (h : ((f : ↥F₀) : F) ∈ W), w - ⟨_, h⟩ ∈ maximalIdeal ↥W) ∧
      (∀ f : F, f ≠ 0 → ∃ c : ↥L, (c : F) ≠ 0 ∧ ∃ h : (c : F) * f ∈ W, IsUnit (⟨_, h⟩ : ↥W)) := by sorry
