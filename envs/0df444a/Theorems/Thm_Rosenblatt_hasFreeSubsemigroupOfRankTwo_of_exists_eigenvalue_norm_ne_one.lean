-- Prove2me | Theorems.Thm_Rosenblatt_hasFreeSubsemigroupOfRankTwo_of_exists_eigenvalue_norm_ne_one
-- name    : Rosenblatt.hasFreeSubsemigroupOfRankTwo_of_exists_eigenvalue_norm_ne_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-21T16:58:55.111649+00:00
-- url     : https://prove2.me/theorems/c248be3f-d4e1-4d3b-9cbe-fdb2dcc81b2c
-- title:
--   Theorem 4.17: if conjugation on a free abelian normal subgroup has an eigenvalue off the unit circle then the group has a free subsemigroup of rank two
-- statement:
--   Let $G$ be a group with a **normal** subgroup $A$ carrying an isomorphism
--   $A \cong \mathbb{Z}^r$ — so $A$ is free abelian of rank $r$. Let $g \in G$ and let $T$ be an
--   $r \times r$ integer matrix representing conjugation by $g$ through that isomorphism: writing
--   $\iota$ for the isomorphism $\mathbb{Z}^r \to A \le G$, for every $z \in \mathbb{Z}^r$
--   $$g \cdot \iota(z) \cdot g^{-1} = \iota(Tz).$$
--   If the complexification of $T$ has an eigenvalue $\varphi$ — a nonzero $v \in \mathbb{C}^r$ with
--   $Tv = \varphi v$ — whose modulus is **not** $1$, then $G$ contains a free subsemigroup of rank
--   two.
--
--   *Reading the pieces.* $\mathbb{Z}^r$ appears as `Multiplicative (Fin r → ℤ)`, the additive group
--   written multiplicatively, so the isomorphism hypothesis says exactly "free abelian of rank $r$";
--   `ofAdd` and `toAdd` are relabelings, not exponentials. The matrix acts on column vectors from
--   the left, $(Tz)_i = \sum_j T_{ij} z_j$. The hypothesis on $\varphi$ is a **disequality**
--   $\lVert\varphi\rVert \neq 1$, not $\lVert\varphi\rVert > 1$; Rosenblatt reduces the case
--   $\lVert\varphi\rVert < 1$ to the other by replacing $g$ with $g^{-1}$. The conclusion is the
--   published `Chou.HasFreeSubsemigroupOfRankTwo`: some pair of elements makes distinct **positive**
--   words take distinct values. No letter stands for an inverse, so this is a free sub*semigroup*
--   claim, not a free subgroup claim.
--
--   *The conjugation hypothesis, precisely.* It constrains only the direction
--   $x \mapsto g x g^{-1}$. Since the isomorphism is onto $A$, it says exactly that conjugation by
--   $g$ maps $A$ into $A$ and is given by $z \mapsto Tz$ in coordinates. At $z = 0$ it holds
--   automatically.
--
--   *Normality is load-bearing, and the statement is vacuous for small $r$.* Together with the
--   conjugation hypothesis, normality forces $z \mapsto Tz$ to be onto $\mathbb{Z}^r$, hence
--   $\det T = \pm 1$. Two consequences follow, both easy to miss. Normality cannot be dropped:
--   without it the remaining hypotheses are satisfiable at $r = 1$, with $T = (2)$ and
--   $\varphi = 2$. And with it the hypotheses are **contradictory for $r \le 1$** — at $r = 0$ there
--   is no nonzero $v$, and at $r = 1$ invertibility forces $T = (\pm 1)$, so $\varphi = \pm 1$ and
--   $\lVert\varphi\rVert = 1$. The theorem therefore has content only from $r = 2$ on.
--
--   The hypotheses are satisfiable there: take $G = \mathbb{Z}^2 \rtimes \mathbb{Z}$ with
--   $T = \begin{pmatrix} 2 & 1 \\ 1 & 1\end{pmatrix}$, whose eigenvalue $(3+\sqrt 5)/2$ has modulus
--   greater than $1$. The hypotheses also force $g \notin A$ and $G$ nonabelian.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, Theorem 4.17, p. 47

import Definitions.Def_Chou_Growth
import Mathlib

namespace Rosenblatt

open scoped Matrix

theorem hasFreeSubsemigroupOfRankTwo_of_exists_eigenvalue_norm_ne_one {G : Type*} [Group G]
    {r : ℕ} (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin r → ℤ))
    (g : G) (T : Matrix (Fin r) (Fin r) ℤ)
    (hT : ∀ z : Fin r → ℤ,
      g * ((e.symm (Multiplicative.ofAdd z) : A) : G) * g⁻¹
        = ((e.symm (Multiplicative.ofAdd (T *ᵥ z)) : A) : G))
    (φ : ℂ) (v : Fin r → ℂ) (hv : v ≠ 0)
    (hev : (T.map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v) (hφ : ‖φ‖ ≠ 1) :
    Chou.HasFreeSubsemigroupOfRankTwo G := by
  sorry

end Rosenblatt
