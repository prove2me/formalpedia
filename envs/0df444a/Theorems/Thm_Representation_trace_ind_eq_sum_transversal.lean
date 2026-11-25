-- Prove2me | Theorems.Thm_Representation_trace_ind_eq_sum_transversal
-- name    : Representation.trace_ind_eq_sum_transversal
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:02:16.115251+00:00
-- url     : https://prove2.me/theorems/076356bc-7935-400f-9795-e9de01b42262
-- title:
--   Frobenius character formula for induced representations over any commutative ring: the trace of g on Ind_H^G V is a sum over coset representatives
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $H \le G$ a subgroup of finite index. Let $\rho\colon H \to \mathrm{GL}_k(V)$ be a $k$-linear representation of $H$ on a finitely generated free $k$-module $V$, and let $\operatorname{Ind}_H^G V$ be the induced representation: the module of coinvariants $(k[G] \otimes_k V)_H$ for the action $h \cdot (x \otimes v) = hx \otimes \rho(h)v$, on which $g \in G$ acts by $[x \otimes v] \mapsto [x g^{-1} \otimes v]$. Let $t\colon G/H \to G$ be any choice of representatives of the left cosets, i.e. $t(c) \in c$ for every $c \in G/H$. Then $\operatorname{Ind}_H^G V$ is a finitely generated free $k$-module, and for every $g \in G$
--
--   $$\operatorname{Tr}\big(g \mid \operatorname{Ind}_H^G V\big) = \sum_{c \in G/H} \dot\chi_\rho\big(t(c)^{-1}\, g\, t(c)\big),$$
--
--   where $\dot\chi_\rho(x) = \operatorname{Tr}\big(\rho(x) \mid V\big)$ for $x \in H$ and $\dot\chi_\rho(x) = 0$ for $x \in G \setminus H$.
--
--   This is Frobenius' formula for the character of an induced representation, proved here over an arbitrary commutative coefficient ring (for instance $\mathbb{Z}/\ell^n$ or $\mathbb{Z}_\ell$) and for an arbitrary, possibly infinite, group $G$ with a subgroup of finite index (for instance a profinite Galois group and an open subgroup). No division by $|H|$ or $|G|$ occurs, so no assumption on the characteristic or on the finiteness of $G$ is needed. It computes the traces of Frobenius elements on induced Galois representations, such as the pushforward of a lisse sheaf along a finite étale Galois cover.
--
--   **Formalization Note**: The induced representation is Mathlib's `Representation.ind H.subtype ρ` on the module `Representation.IndV H.subtype ρ`, which is the coinvariant module $(k[G] \otimes_k V)_H$ described above. Finite index is expressed by `[Fintype (G ⧸ H)]`, where `G ⧸ H` is the type of left cosets $gH$. The coset representatives are the function `t` with `ht : ∀ c, ((t c : G) : G ⧸ H) = c`. The extension by zero $\dot\chi_\rho$ is the `if h : (t c)⁻¹ * g * t c ∈ H then LinearMap.trace k V (ρ ⟨_, h⟩) else 0` term, with classical decidability (`open scoped Classical` in the preamble). Since Mathlib's `LinearMap.trace` is defined to be $0$ on modules that are not finite free, the statement also asserts `Module.Free` and `Module.Finite` for `IndV H.subtype ρ`, which makes the trace formula meaningful. The ring, the group and the module may live in three different universes `u`, `v`, `w`.
-- source:
--   F. G. Frobenius, Über Relationen zwischen den Charakteren einer Gruppe und denen ihrer Untergruppen, Sitzungsber. Preuss. Akad. Wiss. (1898); J.-P. Serre, Linear Representations of Finite Groups, Springer GTM 42 (1977), §7.2, Theorem 12; C. W. Curtis and I. Reiner, Methods of Representation Theory I, Wiley (1981), §10

import Mathlib

set_option autoImplicit false

universe u v w

open scoped Classical

theorem Representation.trace_ind_eq_sum_transversal {k : Type u} {G : Type v} {V : Type w}
    [CommRing k] [Group G] [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V]
    (H : Subgroup G) [Fintype (G ⧸ H)] (ρ : Representation k H V)
    (t : G ⧸ H → G) (ht : ∀ c : G ⧸ H, ((t c : G) : G ⧸ H) = c) :
    Module.Free k (Representation.IndV H.subtype ρ) ∧
      Module.Finite k (Representation.IndV H.subtype ρ) ∧
      ∀ g : G,
        LinearMap.trace k (Representation.IndV H.subtype ρ) (Representation.ind H.subtype ρ g) =
          ∑ c : G ⧸ H,
            if h : (t c)⁻¹ * g * t c ∈ H then LinearMap.trace k V (ρ ⟨(t c)⁻¹ * g * t c, h⟩)
            else 0 := by
  sorry
