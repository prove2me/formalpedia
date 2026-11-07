-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_17
-- name    : TimeSpaceMA.lemma_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:59:18.069027+00:00
-- url     : https://prove2.me/theorems/13b5575d-e569-4ce5-bb5e-16ce001f9527
-- title:
--   Lemma 3.17 — properties of honest tables
-- statement:
--   Let $Y=G^{\otimes m}y$ for integer vectors $y_p$, and let $\Phi$ be an integer bilinear form.
--
--   1. $R_j$ is a tensor codeword on $2(m-j)$ axes: $R_j=G^{\otimes2(m-j)}Z_j$, with $Z_j(\alpha',\beta')=\sum_{h\in[q]^j}\Phi(y_{h\alpha'},y_{h\beta'})$ for $\alpha',\beta'\in[q]^{m-j}$ and $0\le j\le m-1$.
--   2. (Trace identity.) For $1\le j\le m-1$ and all $\alpha,\beta\in[L]^{m-j}$,
--   $$R_j(\alpha,\beta)=\sum_{\ell\in[q]}R_{j-1}\bigl(\sigma(\ell)\alpha,\sigma(\ell)\beta\bigr).$$
--   3. $\sum_{\ell\in[q]}R_{m-1}(\sigma(\ell),\sigma(\ell))=\sum_{p\in[q]^m}\Phi(y_p,y_p)$.
--
--   Differences from the source:
--   - generalization: G the code of Lemma 3.10; Φ from Lemma 3.8(c); y_p = (v_p, u_p) of §3.4 → any systematic subset-sum code, any integer bilinear form on ℤ^D, any integer vectors; reason: the proof on p.14 uses only systematicity and bilinearity, and the page's objects are instances
--   - encoding: level j = 0, …, m−1 with tuples in [L]^{m−j} → level n = m − j, with 1 ≤ n ≤ m; R_{j−1} is level n+1; the axes 2(m−j) are Fin (n+n); reason: this avoids a cast between Fin (m−j) and Fin (m−(j−1))
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.17, p.14

import Definitions.Def_TimeSpaceMA_honestTable

namespace TimeSpaceMA

/-- **Lemma 3.17** (Properties of honest tables; Williams, Xi, STOC 2027 submission, manuscript sha256
184c2f95…, p.14). With `Y = G^{⊗m} y` and `Φ` an integer bilinear form: (a) `R_j` is a tensor codeword on
`2(m − j)` axes with source `Z_j`; (b) the trace identity (2); (c) the final sum is `Σ_p Φ(y_p, y_p)`.

**Formalization Note** Levels are indexed by `n = m − j`: (a) is for `1 ≤ n ≤ m` (`0 ≤ j ≤ m − 1`), (b) for
`1 ≤ n`, `n + 1 ≤ m` (`1 ≤ j ≤ m − 1`), and in (b) `R_{j−1}` is level `n + 1`. In (a) the `2(m − j)` axes are
`Fin (n + n)`, with `(α, β)` the tuple `Fin.append α β`. `G` is any systematic subset-sum code, `Φ` any integer
bilinear form. -/
theorem lemma_3_17 {q L m D : ℕ} (G : SubsetSumCode q L) (σ : Fin q → Fin L)
    (hσ : G.IsSystematic σ) (y : (Fin m → Fin q) → Fin D → ℤ)
    (Φ : (Fin D → ℤ) →ₗ[ℤ] (Fin D → ℤ) →ₗ[ℤ] ℤ) (hm : 1 ≤ m) :
    (∀ (n : ℕ) (hn : n ≤ m), 1 ≤ n → ∀ α β : Fin n → Fin L,
      honestTable σ (tensorEncode G y) Φ n hn α β =
        tensorEncode G
          (fun p : Fin (n + n) → Fin q =>
            honestSource y Φ n hn (fun i => p (Fin.castAdd n i)) (fun i => p (Fin.natAdd n i)))
          (Fin.append α β)) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (hn' : n + 1 ≤ m) (α β : Fin n → Fin L),
      honestTable σ (tensorEncode G y) Φ n (by omega) α β =
        ∑ ℓ : Fin q, honestTable σ (tensorEncode G y) Φ (n + 1) hn'
          (Fin.cons (σ ℓ) α) (Fin.cons (σ ℓ) β)) ∧
    ∑ ℓ : Fin q, honestTable σ (tensorEncode G y) Φ 1 hm (fun _ => σ ℓ) (fun _ => σ ℓ) =
      ∑ p : Fin m → Fin q, Φ (y p) (y p) := by sorry

end TimeSpaceMA
