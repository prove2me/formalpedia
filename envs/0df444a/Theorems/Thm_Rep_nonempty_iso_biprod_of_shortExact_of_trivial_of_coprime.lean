-- Prove2me | Theorems.Thm_Rep_nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime
-- name    : Rep.nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/7cbcfa1a-d640-516e-a03d-38e8c664e32c
-- title:
--   Maschke splitting for representations trivial on Λ
-- statement:
--   Let $p$ be a prime, let $\Gamma$ be a group, and let $\Lambda \le \Gamma$ be a normal subgroup whose quotient $\Gamma/\Lambda$ is finite and whose order $\#(\Gamma/\Lambda)$ is coprime to $p$. Let $X$ be a short complex in the category $\mathrm{Rep}\,(\mathbb{Z}/p)\,\Gamma$ of representations of $\Gamma$ on $\mathbb{Z}/p$-modules, say $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$, assumed short exact in the sense of Mathlib's `ShortComplex.ShortExact` (i.e. $f$ is a monomorphism, $g$ is an epimorphism, and the complex is exact), with $X_2$ finite-dimensional over $\mathbb{Z}/p$, and suppose that every $s \in \Lambda$ acts on $X_2$ by the identity, $\rho_{X_2}(s) = 1$. The conclusion is that the type of isomorphisms $X_2 \cong X_1 \boxplus X_3$ in $\mathrm{Rep}\,(\mathbb{Z}/p)\,\Gamma$ is nonempty: there exists an isomorphism of $\Gamma$-representations between $X_2$ and the binary biproduct of $X_1$ and $X_3$.
--
--   This is Maschke's theorem transported through the quotient map $\Gamma \to \Gamma/\Lambda$: representations of $\Gamma$ on $\mathbb{F}_p$-vector spaces that are trivial on $\Lambda$ behave semisimply as soon as $[\Gamma : \Lambda]$ is prime to $p$, so short exact sequences of such representations split. Coprimality is essential (for $\Gamma = C_p$, $\Lambda = 1$ the sequence $0 \to \mathbf{1} \to \mathbb{F}_p[C_p] \to \cdots$ does not split); the result is used for a dimension count of tensor invariants and in the construction of a biproduct decomposition of a cyclotomic quotient representation attached to $H^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module Limits
open scoped Classical

theorem Rep.nonempty_iso_biprod_of_shortExact_of_trivial_of_coprime
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] (Λ : Subgroup Γ) [Λ.Normal] [Finite (Γ ⧸ Λ)]
    (hcop : (Nat.card (Γ ⧸ Λ)).Coprime p)
    (X : ShortComplex (Rep.{0} (ZMod p) Γ)) (hX : X.ShortExact) [FiniteDimensional (ZMod p) X.X₂]
    (h₂ : ∀ s ∈ Λ, X.X₂.ρ s = 1) :
    Nonempty (X.X₂ ≅ X.X₁ ⊞ X.X₃) := by sorry
