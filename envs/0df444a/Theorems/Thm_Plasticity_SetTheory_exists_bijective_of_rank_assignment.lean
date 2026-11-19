-- Prove2me | Theorems.Thm_Plasticity_SetTheory_exists_bijective_of_rank_assignment
-- name    : Plasticity.SetTheory.exists_bijective_of_rank_assignment
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T19:24:29.550799+00:00
-- url     : https://prove2.me/theorems/575f7856-0a6b-4704-a09a-4ed6188c4713
-- title:
--   Assigning labels block by block: a ranked family of injections completed to a bijection
-- statement:
--   Let $P$, $T$, $K$ be sets with $T$ nonempty, $r\colon P\to\mathbb N$, $\rho\colon T\to\mathbb N$, and for each labelling $y\colon\mathbb N\times K\to T$ let $\Phi_y\colon P\to T$ be injective with $\rho(\Phi_y(p))=r(p)$, where $\Phi_y(p)$ depends only on the labels $y(m,k)$ with $m<r(p)$.
--   Suppose that for every $y$ and $n$ the set $\{t:\rho(t)=n\}\setminus\Phi_y(\{p:r(p)=n\})$ has the cardinality of $K$.
--   Then for some $y$ the map $P\sqcup(\mathbb N\times K)\to T$ given by $\Phi_y$ on $P$ and $y$ on $\mathbb N\times K$ is a bijection.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction A (assigning the labels), abstracted

import Mathlib.SetTheory.Cardinal.Basic

universe u v

namespace Plasticity
theorem SetTheory.exists_bijective_of_rank_assignment {P : Type v} {T K : Type u} [Nonempty T]
    (Φ : (ℕ × K → T) → P → T) (r : P → ℕ) (ρ : T → ℕ)
    (hdep : ∀ y y' p, (∀ m k, m < r p → y (m, k) = y' (m, k)) → Φ y p = Φ y' p)
    (hrank : ∀ y p, ρ (Φ y p) = r p)
    (hinj : ∀ y, Function.Injective (Φ y))
    (hcard : ∀ y n, Cardinal.mk ↥({t | ρ t = n} \ Φ y '' {p | r p = n}) = Cardinal.mk K) :
    ∃ y : ℕ × K → T, Function.Bijective (Sum.elim (Φ y) y) := by sorry
end Plasticity
